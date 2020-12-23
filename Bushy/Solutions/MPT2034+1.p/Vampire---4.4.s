%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : waybel_9__t33_waybel_9.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:09 EDT 2019

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :  158 (7380 expanded)
%              Number of leaves         :   13 (2412 expanded)
%              Depth                    :   40
%              Number of atoms          :  990 (111279 expanded)
%              Number of equality atoms :   18 (6229 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14948,plain,(
    $false ),
    inference(subsumption_resolution,[],[f14939,f14847])).

fof(f14847,plain,(
    r2_hidden(sK2,k10_yellow_6(sK0,sK4(sK0,sK3(sK0,sK1,sK2),sK2))) ),
    inference(subsumption_resolution,[],[f14846,f83])).

fof(f83,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,
    ( ~ r2_hidden(sK2,k10_yellow_6(sK0,sK1))
    & r3_waybel_9(sK0,sK1,sK2)
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & ! [X3] :
        ( ! [X4] :
            ( X3 = X4
            | ~ r3_waybel_9(sK0,sK1,X4)
            | ~ r3_waybel_9(sK0,sK1,X3)
            | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    & l1_waybel_0(sK1,sK0)
    & v7_waybel_0(sK1)
    & v4_orders_2(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v1_compts_1(sK0)
    & v8_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f62,f65,f64,f63])).

fof(f63,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r2_hidden(X2,k10_yellow_6(X0,X1))
                & r3_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & ! [X3] :
                ( ! [X4] :
                    ( X3 = X4
                    | ~ r3_waybel_9(X0,X1,X4)
                    | ~ r3_waybel_9(X0,X1,X3)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v1_compts_1(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X2,k10_yellow_6(sK0,X1))
              & r3_waybel_9(sK0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & ! [X3] :
              ( ! [X4] :
                  ( X3 = X4
                  | ~ r3_waybel_9(sK0,X1,X4)
                  | ~ r3_waybel_9(sK0,X1,X3)
                  | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
              | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
          & l1_waybel_0(X1,sK0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v1_compts_1(sK0)
      & v8_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X2,k10_yellow_6(X0,X1))
              & r3_waybel_9(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & ! [X3] :
              ( ! [X4] :
                  ( X3 = X4
                  | ~ r3_waybel_9(X0,X1,X4)
                  | ~ r3_waybel_9(X0,X1,X3)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ~ r2_hidden(X2,k10_yellow_6(X0,sK1))
            & r3_waybel_9(X0,sK1,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & ! [X3] :
            ( ! [X4] :
                ( X3 = X4
                | ~ r3_waybel_9(X0,sK1,X4)
                | ~ r3_waybel_9(X0,sK1,X3)
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        & l1_waybel_0(sK1,X0)
        & v7_waybel_0(sK1)
        & v4_orders_2(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,k10_yellow_6(X0,X1))
          & r3_waybel_9(X0,X1,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK2,k10_yellow_6(X0,X1))
        & r3_waybel_9(X0,X1,sK2)
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X2,k10_yellow_6(X0,X1))
              & r3_waybel_9(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & ! [X3] :
              ( ! [X4] :
                  ( X3 = X4
                  | ~ r3_waybel_9(X0,X1,X4)
                  | ~ r3_waybel_9(X0,X1,X3)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v1_compts_1(X0)
      & v8_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X4] :
              ( ~ r2_hidden(X4,k10_yellow_6(X0,X1))
              & r3_waybel_9(X0,X1,X4)
              & m1_subset_1(X4,u1_struct_0(X0)) )
          & ! [X2] :
              ( ! [X3] :
                  ( X2 = X3
                  | ~ r3_waybel_9(X0,X1,X3)
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v1_compts_1(X0)
      & v8_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X4] :
              ( ~ r2_hidden(X4,k10_yellow_6(X0,X1))
              & r3_waybel_9(X0,X1,X4)
              & m1_subset_1(X4,u1_struct_0(X0)) )
          & ! [X2] :
              ( ! [X3] :
                  ( X2 = X3
                  | ~ r3_waybel_9(X0,X1,X3)
                  | ~ r3_waybel_9(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v1_compts_1(X0)
      & v8_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_compts_1(X0)
          & v8_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ( ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( ( r3_waybel_9(X0,X1,X3)
                          & r3_waybel_9(X0,X1,X2) )
                       => X2 = X3 ) ) )
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X0))
                 => ( r3_waybel_9(X0,X1,X4)
                   => r2_hidden(X4,k10_yellow_6(X0,X1)) ) ) ) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_compts_1(X0)
          & v8_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ( ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( ( r3_waybel_9(X0,X1,X3)
                          & r3_waybel_9(X0,X1,X2) )
                       => X2 = X3 ) ) )
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ( r3_waybel_9(X0,X1,X2)
                   => r2_hidden(X2,k10_yellow_6(X0,X1)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_compts_1(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ( ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r3_waybel_9(X0,X1,X3)
                        & r3_waybel_9(X0,X1,X2) )
                     => X2 = X3 ) ) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r3_waybel_9(X0,X1,X2)
                 => r2_hidden(X2,k10_yellow_6(X0,X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t33_waybel_9.p',t33_waybel_9)).

fof(f14846,plain,
    ( r2_hidden(sK2,k10_yellow_6(sK0,sK4(sK0,sK3(sK0,sK1,sK2),sK2)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f14845,f84])).

fof(f84,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f66])).

fof(f14845,plain,
    ( r2_hidden(sK2,k10_yellow_6(sK0,sK4(sK0,sK3(sK0,sK1,sK2),sK2)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f14844,f87])).

fof(f87,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f66])).

fof(f14844,plain,
    ( r2_hidden(sK2,k10_yellow_6(sK0,sK4(sK0,sK3(sK0,sK1,sK2),sK2)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f14843,f1025])).

fof(f1025,plain,(
    ~ v2_struct_0(sK3(sK0,sK1,sK2)) ),
    inference(resolution,[],[f472,f351])).

fof(f351,plain,(
    ! [X7] :
      ( ~ m2_yellow_6(X7,sK0,sK1)
      | ~ v2_struct_0(X7) ) ),
    inference(subsumption_resolution,[],[f350,f83])).

fof(f350,plain,(
    ! [X7] :
      ( ~ v2_struct_0(X7)
      | ~ m2_yellow_6(X7,sK0,sK1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f349,f187])).

fof(f187,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f87,f120])).

fof(f120,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t33_waybel_9.p',dt_l1_pre_topc)).

fof(f349,plain,(
    ! [X7] :
      ( ~ v2_struct_0(X7)
      | ~ m2_yellow_6(X7,sK0,sK1)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f348,f88])).

fof(f88,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f66])).

fof(f348,plain,(
    ! [X7] :
      ( ~ v2_struct_0(X7)
      | ~ m2_yellow_6(X7,sK0,sK1)
      | v2_struct_0(sK1)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f347,f89])).

fof(f89,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f66])).

fof(f347,plain,(
    ! [X7] :
      ( ~ v2_struct_0(X7)
      | ~ m2_yellow_6(X7,sK0,sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f286,f90])).

fof(f90,plain,(
    v7_waybel_0(sK1) ),
    inference(cnf_transformation,[],[f66])).

fof(f286,plain,(
    ! [X7] :
      ( ~ v2_struct_0(X7)
      | ~ m2_yellow_6(X7,sK0,sK1)
      | ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f91,f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(X2)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( l1_waybel_0(X2,X0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) )
          | ~ m2_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( l1_waybel_0(X2,X0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) )
          | ~ m2_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m2_yellow_6(X2,X0,X1)
         => ( l1_waybel_0(X2,X0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t33_waybel_9.p',dt_m2_yellow_6)).

fof(f91,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f66])).

fof(f472,plain,(
    m2_yellow_6(sK3(sK0,sK1,sK2),sK0,sK1) ),
    inference(subsumption_resolution,[],[f471,f83])).

fof(f471,plain,
    ( m2_yellow_6(sK3(sK0,sK1,sK2),sK0,sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f470,f84])).

fof(f470,plain,
    ( m2_yellow_6(sK3(sK0,sK1,sK2),sK0,sK1)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f469,f87])).

fof(f469,plain,
    ( m2_yellow_6(sK3(sK0,sK1,sK2),sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f468,f88])).

fof(f468,plain,
    ( m2_yellow_6(sK3(sK0,sK1,sK2),sK0,sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f467,f89])).

fof(f467,plain,
    ( m2_yellow_6(sK3(sK0,sK1,sK2),sK0,sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f466,f90])).

fof(f466,plain,
    ( m2_yellow_6(sK3(sK0,sK1,sK2),sK0,sK1)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f465,f91])).

fof(f465,plain,
    ( m2_yellow_6(sK3(sK0,sK1,sK2),sK0,sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f462,f93])).

fof(f93,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f66])).

fof(f462,plain,
    ( m2_yellow_6(sK3(sK0,sK1,sK2),sK0,sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_waybel_0(sK1,sK0)
    | ~ v7_waybel_0(sK1)
    | ~ v4_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f95,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( m2_yellow_6(sK3(X0,X1,X2),X0,X1)
      | r2_hidden(X2,k10_yellow_6(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ! [X4] :
                    ( ~ r2_hidden(X2,k10_yellow_6(X0,X4))
                    | ~ m2_yellow_6(X4,X0,sK3(X0,X1,X2)) )
                & m2_yellow_6(sK3(X0,X1,X2),X0,X1) )
              | r2_hidden(X2,k10_yellow_6(X0,X1))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f42,f67])).

fof(f67,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r2_hidden(X2,k10_yellow_6(X0,X4))
              | ~ m2_yellow_6(X4,X0,X3) )
          & m2_yellow_6(X3,X0,X1) )
     => ( ! [X4] :
            ( ~ r2_hidden(X2,k10_yellow_6(X0,X4))
            | ~ m2_yellow_6(X4,X0,sK3(X0,X1,X2)) )
        & m2_yellow_6(sK3(X0,X1,X2),X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( ~ r2_hidden(X2,k10_yellow_6(X0,X4))
                      | ~ m2_yellow_6(X4,X0,X3) )
                  & m2_yellow_6(X3,X0,X1) )
              | r2_hidden(X2,k10_yellow_6(X0,X1))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( ~ r2_hidden(X2,k10_yellow_6(X0,X4))
                      | ~ m2_yellow_6(X4,X0,X3) )
                  & m2_yellow_6(X3,X0,X1) )
              | r2_hidden(X2,k10_yellow_6(X0,X1))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ~ ( ! [X3] :
                      ( m2_yellow_6(X3,X0,X1)
                     => ? [X4] :
                          ( r2_hidden(X2,k10_yellow_6(X0,X4))
                          & m2_yellow_6(X4,X0,X3) ) )
                  & ~ r2_hidden(X2,k10_yellow_6(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t33_waybel_9.p',t46_yellow_6)).

fof(f95,plain,(
    ~ r2_hidden(sK2,k10_yellow_6(sK0,sK1)) ),
    inference(cnf_transformation,[],[f66])).

fof(f14843,plain,
    ( r2_hidden(sK2,k10_yellow_6(sK0,sK4(sK0,sK3(sK0,sK1,sK2),sK2)))
    | v2_struct_0(sK3(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f14842,f1024])).

fof(f1024,plain,(
    v4_orders_2(sK3(sK0,sK1,sK2)) ),
    inference(resolution,[],[f472,f356])).

fof(f356,plain,(
    ! [X8] :
      ( ~ m2_yellow_6(X8,sK0,sK1)
      | v4_orders_2(X8) ) ),
    inference(subsumption_resolution,[],[f355,f83])).

fof(f355,plain,(
    ! [X8] :
      ( v4_orders_2(X8)
      | ~ m2_yellow_6(X8,sK0,sK1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f354,f187])).

fof(f354,plain,(
    ! [X8] :
      ( v4_orders_2(X8)
      | ~ m2_yellow_6(X8,sK0,sK1)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f353,f88])).

fof(f353,plain,(
    ! [X8] :
      ( v4_orders_2(X8)
      | ~ m2_yellow_6(X8,sK0,sK1)
      | v2_struct_0(sK1)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f352,f89])).

fof(f352,plain,(
    ! [X8] :
      ( v4_orders_2(X8)
      | ~ m2_yellow_6(X8,sK0,sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f287,f90])).

fof(f287,plain,(
    ! [X8] :
      ( v4_orders_2(X8)
      | ~ m2_yellow_6(X8,sK0,sK1)
      | ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f91,f113])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( v4_orders_2(X2)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f14842,plain,
    ( r2_hidden(sK2,k10_yellow_6(sK0,sK4(sK0,sK3(sK0,sK1,sK2),sK2)))
    | ~ v4_orders_2(sK3(sK0,sK1,sK2))
    | v2_struct_0(sK3(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f14841,f1023])).

fof(f1023,plain,(
    v7_waybel_0(sK3(sK0,sK1,sK2)) ),
    inference(resolution,[],[f472,f361])).

fof(f361,plain,(
    ! [X9] :
      ( ~ m2_yellow_6(X9,sK0,sK1)
      | v7_waybel_0(X9) ) ),
    inference(subsumption_resolution,[],[f360,f83])).

fof(f360,plain,(
    ! [X9] :
      ( v7_waybel_0(X9)
      | ~ m2_yellow_6(X9,sK0,sK1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f359,f187])).

fof(f359,plain,(
    ! [X9] :
      ( v7_waybel_0(X9)
      | ~ m2_yellow_6(X9,sK0,sK1)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f358,f88])).

fof(f358,plain,(
    ! [X9] :
      ( v7_waybel_0(X9)
      | ~ m2_yellow_6(X9,sK0,sK1)
      | v2_struct_0(sK1)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f357,f89])).

fof(f357,plain,(
    ! [X9] :
      ( v7_waybel_0(X9)
      | ~ m2_yellow_6(X9,sK0,sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f288,f90])).

fof(f288,plain,(
    ! [X9] :
      ( v7_waybel_0(X9)
      | ~ m2_yellow_6(X9,sK0,sK1)
      | ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f91,f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( v7_waybel_0(X2)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f14841,plain,
    ( r2_hidden(sK2,k10_yellow_6(sK0,sK4(sK0,sK3(sK0,sK1,sK2),sK2)))
    | ~ v7_waybel_0(sK3(sK0,sK1,sK2))
    | ~ v4_orders_2(sK3(sK0,sK1,sK2))
    | v2_struct_0(sK3(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f14840,f1022])).

fof(f1022,plain,(
    l1_waybel_0(sK3(sK0,sK1,sK2),sK0) ),
    inference(resolution,[],[f472,f366])).

fof(f366,plain,(
    ! [X10] :
      ( ~ m2_yellow_6(X10,sK0,sK1)
      | l1_waybel_0(X10,sK0) ) ),
    inference(subsumption_resolution,[],[f365,f83])).

fof(f365,plain,(
    ! [X10] :
      ( l1_waybel_0(X10,sK0)
      | ~ m2_yellow_6(X10,sK0,sK1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f364,f187])).

fof(f364,plain,(
    ! [X10] :
      ( l1_waybel_0(X10,sK0)
      | ~ m2_yellow_6(X10,sK0,sK1)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f363,f88])).

fof(f363,plain,(
    ! [X10] :
      ( l1_waybel_0(X10,sK0)
      | ~ m2_yellow_6(X10,sK0,sK1)
      | v2_struct_0(sK1)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f362,f89])).

fof(f362,plain,(
    ! [X10] :
      ( l1_waybel_0(X10,sK0)
      | ~ m2_yellow_6(X10,sK0,sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f289,f90])).

fof(f289,plain,(
    ! [X10] :
      ( l1_waybel_0(X10,sK0)
      | ~ m2_yellow_6(X10,sK0,sK1)
      | ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f91,f115])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(X2,X0)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f14840,plain,
    ( r2_hidden(sK2,k10_yellow_6(sK0,sK4(sK0,sK3(sK0,sK1,sK2),sK2)))
    | ~ l1_waybel_0(sK3(sK0,sK1,sK2),sK0)
    | ~ v7_waybel_0(sK3(sK0,sK1,sK2))
    | ~ v4_orders_2(sK3(sK0,sK1,sK2))
    | v2_struct_0(sK3(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f14827,f93])).

fof(f14827,plain,
    ( r2_hidden(sK2,k10_yellow_6(sK0,sK4(sK0,sK3(sK0,sK1,sK2),sK2)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_waybel_0(sK3(sK0,sK1,sK2),sK0)
    | ~ v7_waybel_0(sK3(sK0,sK1,sK2))
    | ~ v4_orders_2(sK3(sK0,sK1,sK2))
    | v2_struct_0(sK3(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f14741,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k10_yellow_6(X0,sK4(X0,X1,X2)))
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k10_yellow_6(X0,sK4(X0,X1,X2)))
                & m2_yellow_6(sK4(X0,X1,X2),X0,X1) )
              | ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f44,f69])).

fof(f69,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X2,k10_yellow_6(X0,X3))
          & m2_yellow_6(X3,X0,X1) )
     => ( r2_hidden(X2,k10_yellow_6(X0,sK4(X0,X1,X2)))
        & m2_yellow_6(sK4(X0,X1,X2),X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r2_hidden(X2,k10_yellow_6(X0,X3))
                  & m2_yellow_6(X3,X0,X1) )
              | ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r2_hidden(X2,k10_yellow_6(X0,X3))
                  & m2_yellow_6(X3,X0,X1) )
              | ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ~ ( ! [X3] :
                      ( m2_yellow_6(X3,X0,X1)
                     => ~ r2_hidden(X2,k10_yellow_6(X0,X3)) )
                  & r3_waybel_9(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t33_waybel_9.p',t32_waybel_9)).

fof(f14741,plain,(
    r3_waybel_9(sK0,sK3(sK0,sK1,sK2),sK2) ),
    inference(backward_demodulation,[],[f14739,f1180])).

fof(f1180,plain,(
    r3_waybel_9(sK0,sK3(sK0,sK1,sK2),sK7(sK0,sK3(sK0,sK1,sK2))) ),
    inference(subsumption_resolution,[],[f1179,f83])).

fof(f1179,plain,
    ( r3_waybel_9(sK0,sK3(sK0,sK1,sK2),sK7(sK0,sK3(sK0,sK1,sK2)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1178,f84])).

fof(f1178,plain,
    ( r3_waybel_9(sK0,sK3(sK0,sK1,sK2),sK7(sK0,sK3(sK0,sK1,sK2)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1177,f85])).

fof(f85,plain,(
    v8_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f66])).

fof(f1177,plain,
    ( r3_waybel_9(sK0,sK3(sK0,sK1,sK2),sK7(sK0,sK3(sK0,sK1,sK2)))
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1176,f86])).

fof(f86,plain,(
    v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f66])).

fof(f1176,plain,
    ( r3_waybel_9(sK0,sK3(sK0,sK1,sK2),sK7(sK0,sK3(sK0,sK1,sK2)))
    | ~ v1_compts_1(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1175,f87])).

fof(f1175,plain,
    ( r3_waybel_9(sK0,sK3(sK0,sK1,sK2),sK7(sK0,sK3(sK0,sK1,sK2)))
    | ~ l1_pre_topc(sK0)
    | ~ v1_compts_1(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1174,f1025])).

fof(f1174,plain,
    ( r3_waybel_9(sK0,sK3(sK0,sK1,sK2),sK7(sK0,sK3(sK0,sK1,sK2)))
    | v2_struct_0(sK3(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v1_compts_1(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1173,f1024])).

fof(f1173,plain,
    ( r3_waybel_9(sK0,sK3(sK0,sK1,sK2),sK7(sK0,sK3(sK0,sK1,sK2)))
    | ~ v4_orders_2(sK3(sK0,sK1,sK2))
    | v2_struct_0(sK3(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v1_compts_1(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1123,f1023])).

fof(f1123,plain,
    ( r3_waybel_9(sK0,sK3(sK0,sK1,sK2),sK7(sK0,sK3(sK0,sK1,sK2)))
    | ~ v7_waybel_0(sK3(sK0,sK1,sK2))
    | ~ v4_orders_2(sK3(sK0,sK1,sK2))
    | v2_struct_0(sK3(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v1_compts_1(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f1022,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( r3_waybel_9(X0,X1,sK7(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r3_waybel_9(X0,X1,sK7(X0,X1))
            & m1_subset_1(sK7(X0,X1),u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f49,f75])).

fof(f75,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r3_waybel_9(X0,X1,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( r3_waybel_9(X0,X1,sK7(X0,X1))
        & m1_subset_1(sK7(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( r3_waybel_9(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( r3_waybel_9(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_compts_1(X0)
        & v8_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ? [X2] :
              ( r3_waybel_9(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t33_waybel_9.p',t30_waybel_9)).

fof(f14739,plain,(
    sK2 = sK7(sK0,sK3(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f14731,f1172])).

fof(f1172,plain,(
    m1_subset_1(sK7(sK0,sK3(sK0,sK1,sK2)),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f1171,f83])).

fof(f1171,plain,
    ( m1_subset_1(sK7(sK0,sK3(sK0,sK1,sK2)),u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1170,f84])).

fof(f1170,plain,
    ( m1_subset_1(sK7(sK0,sK3(sK0,sK1,sK2)),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1169,f85])).

fof(f1169,plain,
    ( m1_subset_1(sK7(sK0,sK3(sK0,sK1,sK2)),u1_struct_0(sK0))
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1168,f86])).

fof(f1168,plain,
    ( m1_subset_1(sK7(sK0,sK3(sK0,sK1,sK2)),u1_struct_0(sK0))
    | ~ v1_compts_1(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1167,f87])).

fof(f1167,plain,
    ( m1_subset_1(sK7(sK0,sK3(sK0,sK1,sK2)),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v1_compts_1(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1166,f1025])).

fof(f1166,plain,
    ( m1_subset_1(sK7(sK0,sK3(sK0,sK1,sK2)),u1_struct_0(sK0))
    | v2_struct_0(sK3(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v1_compts_1(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1165,f1024])).

fof(f1165,plain,
    ( m1_subset_1(sK7(sK0,sK3(sK0,sK1,sK2)),u1_struct_0(sK0))
    | ~ v4_orders_2(sK3(sK0,sK1,sK2))
    | v2_struct_0(sK3(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v1_compts_1(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1122,f1023])).

fof(f1122,plain,
    ( m1_subset_1(sK7(sK0,sK3(sK0,sK1,sK2)),u1_struct_0(sK0))
    | ~ v7_waybel_0(sK3(sK0,sK1,sK2))
    | ~ v4_orders_2(sK3(sK0,sK1,sK2))
    | v2_struct_0(sK3(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v1_compts_1(sK0)
    | ~ v8_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f1022,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK7(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f14731,plain,
    ( ~ m1_subset_1(sK7(sK0,sK3(sK0,sK1,sK2)),u1_struct_0(sK0))
    | sK2 = sK7(sK0,sK3(sK0,sK1,sK2)) ),
    inference(resolution,[],[f14712,f1180])).

fof(f14712,plain,(
    ! [X3] :
      ( ~ r3_waybel_9(sK0,sK3(sK0,sK1,sK2),X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | sK2 = X3 ) ),
    inference(duplicate_literal_removal,[],[f14699])).

fof(f14699,plain,(
    ! [X3] :
      ( ~ r3_waybel_9(sK0,sK3(sK0,sK1,sK2),X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | sK2 = X3
      | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f1037,f491])).

fof(f491,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,sK1,X0)
      | sK2 = X0
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f481,f93])).

fof(f481,plain,(
    ! [X0] :
      ( ~ r3_waybel_9(sK0,sK1,X0)
      | sK2 = X0
      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f92,f94])).

fof(f94,plain,(
    r3_waybel_9(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f66])).

fof(f92,plain,(
    ! [X4,X3] :
      ( ~ r3_waybel_9(sK0,sK1,X4)
      | ~ r3_waybel_9(sK0,sK1,X3)
      | X3 = X4
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f1037,plain,(
    ! [X0] :
      ( r3_waybel_9(sK0,sK1,X0)
      | ~ r3_waybel_9(sK0,sK3(sK0,sK1,sK2),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f1036,f83])).

fof(f1036,plain,(
    ! [X0] :
      ( r3_waybel_9(sK0,sK1,X0)
      | ~ r3_waybel_9(sK0,sK3(sK0,sK1,sK2),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1035,f84])).

fof(f1035,plain,(
    ! [X0] :
      ( r3_waybel_9(sK0,sK1,X0)
      | ~ r3_waybel_9(sK0,sK3(sK0,sK1,sK2),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1034,f87])).

fof(f1034,plain,(
    ! [X0] :
      ( r3_waybel_9(sK0,sK1,X0)
      | ~ r3_waybel_9(sK0,sK3(sK0,sK1,sK2),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1033,f88])).

fof(f1033,plain,(
    ! [X0] :
      ( r3_waybel_9(sK0,sK1,X0)
      | ~ r3_waybel_9(sK0,sK3(sK0,sK1,sK2),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1032,f89])).

fof(f1032,plain,(
    ! [X0] :
      ( r3_waybel_9(sK0,sK1,X0)
      | ~ r3_waybel_9(sK0,sK3(sK0,sK1,sK2),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1031,f90])).

fof(f1031,plain,(
    ! [X0] :
      ( r3_waybel_9(sK0,sK1,X0)
      | ~ r3_waybel_9(sK0,sK3(sK0,sK1,sK2),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1030,f91])).

fof(f1030,plain,(
    ! [X0] :
      ( r3_waybel_9(sK0,sK1,X0)
      | ~ r3_waybel_9(sK0,sK3(sK0,sK1,sK2),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_waybel_0(sK1,sK0)
      | ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f472,f104])).

fof(f104,plain,(
    ! [X2,X0,X3,X1] :
      ( r3_waybel_9(X0,X1,X3)
      | ~ r3_waybel_9(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r3_waybel_9(X0,X1,X3)
                  | ~ r3_waybel_9(X0,X2,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m2_yellow_6(X2,X0,X1) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r3_waybel_9(X0,X1,X3)
                  | ~ r3_waybel_9(X0,X2,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m2_yellow_6(X2,X0,X1) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m2_yellow_6(X2,X0,X1)
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r3_waybel_9(X0,X2,X3)
                   => r3_waybel_9(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_9__t33_waybel_9.p',t31_waybel_9)).

fof(f14939,plain,(
    ~ r2_hidden(sK2,k10_yellow_6(sK0,sK4(sK0,sK3(sK0,sK1,sK2),sK2))) ),
    inference(resolution,[],[f14839,f480])).

fof(f480,plain,(
    ! [X0] :
      ( ~ m2_yellow_6(X0,sK0,sK3(sK0,sK1,sK2))
      | ~ r2_hidden(sK2,k10_yellow_6(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f479,f83])).

fof(f479,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2,k10_yellow_6(sK0,X0))
      | ~ m2_yellow_6(X0,sK0,sK3(sK0,sK1,sK2))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f478,f84])).

fof(f478,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2,k10_yellow_6(sK0,X0))
      | ~ m2_yellow_6(X0,sK0,sK3(sK0,sK1,sK2))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f477,f87])).

fof(f477,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2,k10_yellow_6(sK0,X0))
      | ~ m2_yellow_6(X0,sK0,sK3(sK0,sK1,sK2))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f476,f88])).

fof(f476,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2,k10_yellow_6(sK0,X0))
      | ~ m2_yellow_6(X0,sK0,sK3(sK0,sK1,sK2))
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f475,f89])).

fof(f475,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2,k10_yellow_6(sK0,X0))
      | ~ m2_yellow_6(X0,sK0,sK3(sK0,sK1,sK2))
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f474,f90])).

fof(f474,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2,k10_yellow_6(sK0,X0))
      | ~ m2_yellow_6(X0,sK0,sK3(sK0,sK1,sK2))
      | ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f473,f91])).

fof(f473,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2,k10_yellow_6(sK0,X0))
      | ~ m2_yellow_6(X0,sK0,sK3(sK0,sK1,sK2))
      | ~ l1_waybel_0(sK1,sK0)
      | ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f463,f93])).

fof(f463,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2,k10_yellow_6(sK0,X0))
      | ~ m2_yellow_6(X0,sK0,sK3(sK0,sK1,sK2))
      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
      | ~ l1_waybel_0(sK1,sK0)
      | ~ v7_waybel_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f95,f100])).

fof(f100,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X2,k10_yellow_6(X0,X4))
      | ~ m2_yellow_6(X4,X0,sK3(X0,X1,X2))
      | r2_hidden(X2,k10_yellow_6(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f14839,plain,(
    m2_yellow_6(sK4(sK0,sK3(sK0,sK1,sK2),sK2),sK0,sK3(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f14838,f83])).

fof(f14838,plain,
    ( m2_yellow_6(sK4(sK0,sK3(sK0,sK1,sK2),sK2),sK0,sK3(sK0,sK1,sK2))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f14837,f84])).

fof(f14837,plain,
    ( m2_yellow_6(sK4(sK0,sK3(sK0,sK1,sK2),sK2),sK0,sK3(sK0,sK1,sK2))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f14836,f87])).

fof(f14836,plain,
    ( m2_yellow_6(sK4(sK0,sK3(sK0,sK1,sK2),sK2),sK0,sK3(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f14835,f1025])).

fof(f14835,plain,
    ( m2_yellow_6(sK4(sK0,sK3(sK0,sK1,sK2),sK2),sK0,sK3(sK0,sK1,sK2))
    | v2_struct_0(sK3(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f14834,f1024])).

fof(f14834,plain,
    ( m2_yellow_6(sK4(sK0,sK3(sK0,sK1,sK2),sK2),sK0,sK3(sK0,sK1,sK2))
    | ~ v4_orders_2(sK3(sK0,sK1,sK2))
    | v2_struct_0(sK3(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f14833,f1023])).

fof(f14833,plain,
    ( m2_yellow_6(sK4(sK0,sK3(sK0,sK1,sK2),sK2),sK0,sK3(sK0,sK1,sK2))
    | ~ v7_waybel_0(sK3(sK0,sK1,sK2))
    | ~ v4_orders_2(sK3(sK0,sK1,sK2))
    | v2_struct_0(sK3(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f14832,f1022])).

fof(f14832,plain,
    ( m2_yellow_6(sK4(sK0,sK3(sK0,sK1,sK2),sK2),sK0,sK3(sK0,sK1,sK2))
    | ~ l1_waybel_0(sK3(sK0,sK1,sK2),sK0)
    | ~ v7_waybel_0(sK3(sK0,sK1,sK2))
    | ~ v4_orders_2(sK3(sK0,sK1,sK2))
    | v2_struct_0(sK3(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f14826,f93])).

fof(f14826,plain,
    ( m2_yellow_6(sK4(sK0,sK3(sK0,sK1,sK2),sK2),sK0,sK3(sK0,sK1,sK2))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_waybel_0(sK3(sK0,sK1,sK2),sK0)
    | ~ v7_waybel_0(sK3(sK0,sK1,sK2))
    | ~ v4_orders_2(sK3(sK0,sK1,sK2))
    | v2_struct_0(sK3(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f14741,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( m2_yellow_6(sK4(X0,X1,X2),X0,X1)
      | ~ r3_waybel_9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f70])).
%------------------------------------------------------------------------------
