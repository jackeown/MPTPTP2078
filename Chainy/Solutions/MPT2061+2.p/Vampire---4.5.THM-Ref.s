%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT2061+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:40 EST 2020

% Result     : Theorem 5.32s
% Output     : Refutation 5.32s
% Verified   : 
% Statistics : Number of formulae       :   38 ( 289 expanded)
%              Number of leaves         :    7 ( 121 expanded)
%              Depth                    :    8
%              Number of atoms          :  219 (2566 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12094,plain,(
    $false ),
    inference(subsumption_resolution,[],[f12090,f9554])).

fof(f9554,plain,(
    r2_waybel_0(sK39,sK42,k6_subset_1(u1_struct_0(sK39),sK40)) ),
    inference(unit_resulting_resolution,[],[f6114,f6115,f7747,f6122,f7750,f6174])).

fof(f6174,plain,(
    ! [X2,X0,X1] :
      ( r1_waybel_0(X0,X1,X2)
      | r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f5365])).

fof(f5365,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
              & ( ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f4589])).

fof(f4589,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f4588])).

fof(f4588,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3323])).

fof(f3323,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_waybel_0)).

fof(f7750,plain,(
    l1_waybel_0(sK42,sK39) ),
    inference(unit_resulting_resolution,[],[f6114,f6115,f6116,f6117,f6118,f6119,f6121,f6140])).

fof(f6140,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(X2,X0)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4569])).

fof(f4569,plain,(
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
    inference(flattening,[],[f4568])).

fof(f4568,plain,(
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
    inference(ennf_transformation,[],[f3888])).

fof(f3888,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_yellow_6)).

fof(f6121,plain,(
    m2_yellow_6(sK42,sK39,sK41) ),
    inference(cnf_transformation,[],[f5335])).

fof(f5335,plain,
    ( ~ r1_waybel_0(sK39,sK42,sK40)
    & m2_yellow_6(sK42,sK39,sK41)
    & r1_waybel_0(sK39,sK41,sK40)
    & l1_waybel_0(sK41,sK39)
    & v7_waybel_0(sK41)
    & v4_orders_2(sK41)
    & ~ v2_struct_0(sK41)
    & l1_struct_0(sK39)
    & ~ v2_struct_0(sK39) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK39,sK40,sK41,sK42])],[f4561,f5334,f5333,f5332])).

fof(f5332,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( ? [X3] :
                ( ~ r1_waybel_0(X0,X3,X1)
                & m2_yellow_6(X3,X0,X2) )
            & r1_waybel_0(X0,X2,X1)
            & l1_waybel_0(X2,X0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X2,X1] :
          ( ? [X3] :
              ( ~ r1_waybel_0(sK39,X3,X1)
              & m2_yellow_6(X3,sK39,X2) )
          & r1_waybel_0(sK39,X2,X1)
          & l1_waybel_0(X2,sK39)
          & v7_waybel_0(X2)
          & v4_orders_2(X2)
          & ~ v2_struct_0(X2) )
      & l1_struct_0(sK39)
      & ~ v2_struct_0(sK39) ) ),
    introduced(choice_axiom,[])).

fof(f5333,plain,
    ( ? [X2,X1] :
        ( ? [X3] :
            ( ~ r1_waybel_0(sK39,X3,X1)
            & m2_yellow_6(X3,sK39,X2) )
        & r1_waybel_0(sK39,X2,X1)
        & l1_waybel_0(X2,sK39)
        & v7_waybel_0(X2)
        & v4_orders_2(X2)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ~ r1_waybel_0(sK39,X3,sK40)
          & m2_yellow_6(X3,sK39,sK41) )
      & r1_waybel_0(sK39,sK41,sK40)
      & l1_waybel_0(sK41,sK39)
      & v7_waybel_0(sK41)
      & v4_orders_2(sK41)
      & ~ v2_struct_0(sK41) ) ),
    introduced(choice_axiom,[])).

fof(f5334,plain,
    ( ? [X3] :
        ( ~ r1_waybel_0(sK39,X3,sK40)
        & m2_yellow_6(X3,sK39,sK41) )
   => ( ~ r1_waybel_0(sK39,sK42,sK40)
      & m2_yellow_6(sK42,sK39,sK41) ) ),
    introduced(choice_axiom,[])).

fof(f4561,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ? [X3] :
              ( ~ r1_waybel_0(X0,X3,X1)
              & m2_yellow_6(X3,X0,X2) )
          & r1_waybel_0(X0,X2,X1)
          & l1_waybel_0(X2,X0)
          & v7_waybel_0(X2)
          & v4_orders_2(X2)
          & ~ v2_struct_0(X2) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f4560])).

fof(f4560,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ? [X3] :
              ( ~ r1_waybel_0(X0,X3,X1)
              & m2_yellow_6(X3,X0,X2) )
          & r1_waybel_0(X0,X2,X1)
          & l1_waybel_0(X2,X0)
          & v7_waybel_0(X2)
          & v4_orders_2(X2)
          & ~ v2_struct_0(X2) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4528])).

fof(f4528,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1,X2] :
            ( ( l1_waybel_0(X2,X0)
              & v7_waybel_0(X2)
              & v4_orders_2(X2)
              & ~ v2_struct_0(X2) )
           => ( r1_waybel_0(X0,X2,X1)
             => ! [X3] :
                  ( m2_yellow_6(X3,X0,X2)
                 => r1_waybel_0(X0,X3,X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f4527])).

fof(f4527,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( ( l1_waybel_0(X2,X0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) )
         => ( r1_waybel_0(X0,X2,X1)
           => ! [X3] :
                ( m2_yellow_6(X3,X0,X2)
               => r1_waybel_0(X0,X3,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_yellow19)).

fof(f6119,plain,(
    l1_waybel_0(sK41,sK39) ),
    inference(cnf_transformation,[],[f5335])).

fof(f6118,plain,(
    v7_waybel_0(sK41) ),
    inference(cnf_transformation,[],[f5335])).

fof(f6117,plain,(
    v4_orders_2(sK41) ),
    inference(cnf_transformation,[],[f5335])).

fof(f6116,plain,(
    ~ v2_struct_0(sK41) ),
    inference(cnf_transformation,[],[f5335])).

fof(f6122,plain,(
    ~ r1_waybel_0(sK39,sK42,sK40) ),
    inference(cnf_transformation,[],[f5335])).

fof(f7747,plain,(
    ~ v2_struct_0(sK42) ),
    inference(unit_resulting_resolution,[],[f6114,f6115,f6116,f6117,f6118,f6119,f6121,f6137])).

fof(f6137,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(X2)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4569])).

fof(f6115,plain,(
    l1_struct_0(sK39) ),
    inference(cnf_transformation,[],[f5335])).

fof(f6114,plain,(
    ~ v2_struct_0(sK39) ),
    inference(cnf_transformation,[],[f5335])).

fof(f12090,plain,(
    ~ r2_waybel_0(sK39,sK42,k6_subset_1(u1_struct_0(sK39),sK40)) ),
    inference(unit_resulting_resolution,[],[f6114,f6115,f6116,f6117,f6118,f6119,f6121,f7717,f7031])).

fof(f7031,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_waybel_0(X0,X1,X3)
      | ~ r2_waybel_0(X0,X2,X3)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f5049])).

fof(f5049,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_waybel_0(X0,X1,X3)
                  | ~ r2_waybel_0(X0,X2,X3) )
              | ~ m2_yellow_6(X2,X0,X1) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f5048])).

fof(f5048,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_waybel_0(X0,X1,X3)
                  | ~ r2_waybel_0(X0,X2,X3) )
              | ~ m2_yellow_6(X2,X0,X1) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4067])).

fof(f4067,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m2_yellow_6(X2,X0,X1)
             => ! [X3] :
                  ( r2_waybel_0(X0,X2,X3)
                 => r2_waybel_0(X0,X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_yellow_6)).

fof(f7717,plain,(
    ~ r2_waybel_0(sK39,sK41,k6_subset_1(u1_struct_0(sK39),sK40)) ),
    inference(unit_resulting_resolution,[],[f6114,f6115,f6116,f6119,f6120,f6173])).

fof(f6173,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
      | ~ r1_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f5365])).

fof(f6120,plain,(
    r1_waybel_0(sK39,sK41,sK40) ),
    inference(cnf_transformation,[],[f5335])).
%------------------------------------------------------------------------------
