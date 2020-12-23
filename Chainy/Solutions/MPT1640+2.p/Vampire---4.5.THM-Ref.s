%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1640+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:28 EST 2020

% Result     : Theorem 1.33s
% Output     : Refutation 1.33s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 324 expanded)
%              Number of leaves         :    7 ( 131 expanded)
%              Depth                    :   12
%              Number of atoms          :  191 (2424 expanded)
%              Number of equality atoms :   28 ( 689 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3908,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3891,f3886])).

fof(f3886,plain,(
    ~ r1_orders_2(sK4,sK5,sK6) ),
    inference(unit_resulting_resolution,[],[f3369,f3370,f3374,f3371,f3372,f3881,f3395])).

fof(f3395,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ r1_orders_2(X0,X2,X1)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3238])).

fof(f3238,plain,(
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
    inference(flattening,[],[f3237])).

fof(f3237,plain,(
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
    inference(ennf_transformation,[],[f1953])).

fof(f1953,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_orders_2)).

fof(f3881,plain,(
    r1_orders_2(sK4,sK6,sK5) ),
    inference(unit_resulting_resolution,[],[f3371,f3523,f3532])).

fof(f3532,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
      | r1_orders_2(sK4,sK6,X0)
      | ~ r2_hidden(X0,k6_waybel_0(sK4,sK5)) ) ),
    inference(subsumption_resolution,[],[f3531,f3367])).

fof(f3367,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f3299])).

% (3394)Refutation not found, incomplete strategy% (3394)------------------------------
% (3394)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (3394)Termination reason: Refutation not found, incomplete strategy

% (3394)Memory used [KB]: 9466
% (3394)Time elapsed: 0.178 s
% (3394)------------------------------
% (3394)------------------------------
fof(f3299,plain,
    ( sK5 != sK6
    & k6_waybel_0(sK4,sK5) = k6_waybel_0(sK4,sK6)
    & m1_subset_1(sK6,u1_struct_0(sK4))
    & m1_subset_1(sK5,u1_struct_0(sK4))
    & l1_orders_2(sK4)
    & v5_orders_2(sK4)
    & v3_orders_2(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f3214,f3298,f3297,f3296])).

fof(f3296,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( X1 != X2
                & k6_waybel_0(X0,X1) = k6_waybel_0(X0,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k6_waybel_0(sK4,X1) = k6_waybel_0(sK4,X2)
              & m1_subset_1(X2,u1_struct_0(sK4)) )
          & m1_subset_1(X1,u1_struct_0(sK4)) )
      & l1_orders_2(sK4)
      & v5_orders_2(sK4)
      & v3_orders_2(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f3297,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( X1 != X2
            & k6_waybel_0(sK4,X1) = k6_waybel_0(sK4,X2)
            & m1_subset_1(X2,u1_struct_0(sK4)) )
        & m1_subset_1(X1,u1_struct_0(sK4)) )
   => ( ? [X2] :
          ( sK5 != X2
          & k6_waybel_0(sK4,X2) = k6_waybel_0(sK4,sK5)
          & m1_subset_1(X2,u1_struct_0(sK4)) )
      & m1_subset_1(sK5,u1_struct_0(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f3298,plain,
    ( ? [X2] :
        ( sK5 != X2
        & k6_waybel_0(sK4,X2) = k6_waybel_0(sK4,sK5)
        & m1_subset_1(X2,u1_struct_0(sK4)) )
   => ( sK5 != sK6
      & k6_waybel_0(sK4,sK5) = k6_waybel_0(sK4,sK6)
      & m1_subset_1(sK6,u1_struct_0(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f3214,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k6_waybel_0(X0,X1) = k6_waybel_0(X0,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3213])).

fof(f3213,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k6_waybel_0(X0,X1) = k6_waybel_0(X0,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3202])).

fof(f3202,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( k6_waybel_0(X0,X1) = k6_waybel_0(X0,X2)
                 => X1 = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f3201])).

fof(f3201,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( k6_waybel_0(X0,X1) = k6_waybel_0(X0,X2)
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_waybel_0)).

fof(f3531,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k6_waybel_0(sK4,sK5))
      | r1_orders_2(sK4,sK6,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK4))
      | v2_struct_0(sK4) ) ),
    inference(subsumption_resolution,[],[f3530,f3370])).

fof(f3530,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k6_waybel_0(sK4,sK5))
      | r1_orders_2(sK4,sK6,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK4))
      | ~ l1_orders_2(sK4)
      | v2_struct_0(sK4) ) ),
    inference(subsumption_resolution,[],[f3527,f3372])).

fof(f3527,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k6_waybel_0(sK4,sK5))
      | r1_orders_2(sK4,sK6,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK4))
      | ~ m1_subset_1(sK6,u1_struct_0(sK4))
      | ~ l1_orders_2(sK4)
      | v2_struct_0(sK4) ) ),
    inference(superposition,[],[f3376,f3373])).

fof(f3373,plain,(
    k6_waybel_0(sK4,sK5) = k6_waybel_0(sK4,sK6) ),
    inference(cnf_transformation,[],[f3299])).

fof(f3376,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r2_hidden(X2,k6_waybel_0(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3300])).

fof(f3300,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k6_waybel_0(X0,X1))
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( r1_orders_2(X0,X1,X2)
                  | ~ r2_hidden(X2,k6_waybel_0(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3218])).

fof(f3218,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k6_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3217])).

fof(f3217,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k6_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3198])).

fof(f3198,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k6_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_waybel_0)).

fof(f3523,plain,(
    r2_hidden(sK5,k6_waybel_0(sK4,sK5)) ),
    inference(unit_resulting_resolution,[],[f3367,f3370,f3371,f3371,f3505,f3377])).

fof(f3377,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k6_waybel_0(X0,X1))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3300])).

fof(f3505,plain,(
    r1_orders_2(sK4,sK5,sK5) ),
    inference(unit_resulting_resolution,[],[f3367,f3368,f3370,f3371,f3382])).

fof(f3382,plain,(
    ! [X0,X1] :
      ( r1_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3224])).

fof(f3224,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3223])).

fof(f3223,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1952])).

fof(f1952,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,X1,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_orders_2)).

fof(f3368,plain,(
    v3_orders_2(sK4) ),
    inference(cnf_transformation,[],[f3299])).

fof(f3372,plain,(
    m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f3299])).

fof(f3371,plain,(
    m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f3299])).

fof(f3374,plain,(
    sK5 != sK6 ),
    inference(cnf_transformation,[],[f3299])).

fof(f3370,plain,(
    l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f3299])).

fof(f3369,plain,(
    v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f3299])).

fof(f3891,plain,(
    r1_orders_2(sK4,sK5,sK6) ),
    inference(unit_resulting_resolution,[],[f3367,f3370,f3371,f3372,f3540,f3376])).

fof(f3540,plain,(
    r2_hidden(sK6,k6_waybel_0(sK4,sK5)) ),
    inference(forward_demodulation,[],[f3536,f3373])).

fof(f3536,plain,(
    r2_hidden(sK6,k6_waybel_0(sK4,sK6)) ),
    inference(unit_resulting_resolution,[],[f3367,f3370,f3372,f3372,f3514,f3377])).

fof(f3514,plain,(
    r1_orders_2(sK4,sK6,sK6) ),
    inference(unit_resulting_resolution,[],[f3367,f3368,f3370,f3372,f3382])).
%------------------------------------------------------------------------------
