%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1657+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:28 EST 2020

% Result     : Theorem 2.76s
% Output     : Refutation 2.96s
% Verified   : 
% Statistics : Number of formulae       :   89 (3613 expanded)
%              Number of leaves         :    6 ( 934 expanded)
%              Depth                    :   45
%              Number of atoms          :  445 (28642 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4397,plain,(
    $false ),
    inference(subsumption_resolution,[],[f4396,f4150])).

fof(f4150,plain,(
    r1_lattice3(sK2,sK3,sK7(sK2,sK3,k4_waybel_0(sK2,sK3))) ),
    inference(subsumption_resolution,[],[f4149,f3303])).

fof(f3303,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f3277])).

fof(f3277,plain,
    ( ( ~ r2_yellow_0(sK2,k4_waybel_0(sK2,sK3))
      | ~ r2_yellow_0(sK2,sK3) )
    & ( r2_yellow_0(sK2,k4_waybel_0(sK2,sK3))
      | r2_yellow_0(sK2,sK3) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_orders_2(sK2)
    & v4_orders_2(sK2)
    & v3_orders_2(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f3274,f3276,f3275])).

fof(f3275,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r2_yellow_0(X0,k4_waybel_0(X0,X1))
              | ~ r2_yellow_0(X0,X1) )
            & ( r2_yellow_0(X0,k4_waybel_0(X0,X1))
              | r2_yellow_0(X0,X1) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ r2_yellow_0(sK2,k4_waybel_0(sK2,X1))
            | ~ r2_yellow_0(sK2,X1) )
          & ( r2_yellow_0(sK2,k4_waybel_0(sK2,X1))
            | r2_yellow_0(sK2,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_orders_2(sK2)
      & v4_orders_2(sK2)
      & v3_orders_2(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f3276,plain,
    ( ? [X1] :
        ( ( ~ r2_yellow_0(sK2,k4_waybel_0(sK2,X1))
          | ~ r2_yellow_0(sK2,X1) )
        & ( r2_yellow_0(sK2,k4_waybel_0(sK2,X1))
          | r2_yellow_0(sK2,X1) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
   => ( ( ~ r2_yellow_0(sK2,k4_waybel_0(sK2,sK3))
        | ~ r2_yellow_0(sK2,sK3) )
      & ( r2_yellow_0(sK2,k4_waybel_0(sK2,sK3))
        | r2_yellow_0(sK2,sK3) )
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f3274,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r2_yellow_0(X0,k4_waybel_0(X0,X1))
            | ~ r2_yellow_0(X0,X1) )
          & ( r2_yellow_0(X0,k4_waybel_0(X0,X1))
            | r2_yellow_0(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3273])).

fof(f3273,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r2_yellow_0(X0,k4_waybel_0(X0,X1))
            | ~ r2_yellow_0(X0,X1) )
          & ( r2_yellow_0(X0,k4_waybel_0(X0,X1))
            | r2_yellow_0(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3248])).

fof(f3248,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_yellow_0(X0,X1)
          <~> r2_yellow_0(X0,k4_waybel_0(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3247])).

fof(f3247,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_yellow_0(X0,X1)
          <~> r2_yellow_0(X0,k4_waybel_0(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3231])).

fof(f3231,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( r2_yellow_0(X0,X1)
            <=> r2_yellow_0(X0,k4_waybel_0(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f3230])).

fof(f3230,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_yellow_0(X0,X1)
          <=> r2_yellow_0(X0,k4_waybel_0(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_waybel_0)).

fof(f4149,plain,
    ( r1_lattice3(sK2,sK3,sK7(sK2,sK3,k4_waybel_0(sK2,sK3)))
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f4148,f3306])).

fof(f3306,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f3277])).

fof(f4148,plain,
    ( r1_lattice3(sK2,sK3,sK7(sK2,sK3,k4_waybel_0(sK2,sK3)))
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f4147,f4080])).

fof(f4080,plain,(
    ~ r2_yellow_0(sK2,k4_waybel_0(sK2,sK3)) ),
    inference(subsumption_resolution,[],[f4079,f3309])).

fof(f3309,plain,
    ( ~ r2_yellow_0(sK2,sK3)
    | ~ r2_yellow_0(sK2,k4_waybel_0(sK2,sK3)) ),
    inference(cnf_transformation,[],[f3277])).

fof(f4079,plain,
    ( r2_yellow_0(sK2,sK3)
    | ~ r2_yellow_0(sK2,k4_waybel_0(sK2,sK3)) ),
    inference(subsumption_resolution,[],[f4078,f3303])).

fof(f4078,plain,
    ( r2_yellow_0(sK2,sK3)
    | ~ r2_yellow_0(sK2,k4_waybel_0(sK2,sK3))
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f4077,f3306])).

fof(f4077,plain,
    ( r2_yellow_0(sK2,sK3)
    | ~ r2_yellow_0(sK2,k4_waybel_0(sK2,sK3))
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(duplicate_literal_removal,[],[f4076])).

fof(f4076,plain,
    ( r2_yellow_0(sK2,sK3)
    | ~ r2_yellow_0(sK2,k4_waybel_0(sK2,sK3))
    | r2_yellow_0(sK2,sK3)
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f4069,f3328])).

fof(f3328,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | r2_yellow_0(X0,X2)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3290])).

fof(f3290,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ( ( ~ r1_lattice3(X0,X2,sK7(X0,X1,X2))
              | ~ r1_lattice3(X0,X1,sK7(X0,X1,X2)) )
            & ( r1_lattice3(X0,X2,sK7(X0,X1,X2))
              | r1_lattice3(X0,X1,sK7(X0,X1,X2)) )
            & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f3288,f3289])).

fof(f3289,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r1_lattice3(X0,X2,X3)
            | ~ r1_lattice3(X0,X1,X3) )
          & ( r1_lattice3(X0,X2,X3)
            | r1_lattice3(X0,X1,X3) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ( ~ r1_lattice3(X0,X2,sK7(X0,X1,X2))
          | ~ r1_lattice3(X0,X1,sK7(X0,X1,X2)) )
        & ( r1_lattice3(X0,X2,sK7(X0,X1,X2))
          | r1_lattice3(X0,X1,sK7(X0,X1,X2)) )
        & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3288,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ? [X3] :
              ( ( ~ r1_lattice3(X0,X2,X3)
                | ~ r1_lattice3(X0,X1,X3) )
              & ( r1_lattice3(X0,X2,X3)
                | r1_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3287])).

fof(f3287,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ? [X3] :
              ( ( ~ r1_lattice3(X0,X2,X3)
                | ~ r1_lattice3(X0,X1,X3) )
              & ( r1_lattice3(X0,X2,X3)
                | r1_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3263])).

fof(f3263,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ? [X3] :
              ( ( r1_lattice3(X0,X1,X3)
              <~> r1_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3262])).

fof(f3262,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ? [X3] :
              ( ( r1_lattice3(X0,X1,X3)
              <~> r1_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3045])).

fof(f3045,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( ( r2_yellow_0(X0,X1)
            & ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r1_lattice3(X0,X1,X3)
                <=> r1_lattice3(X0,X2,X3) ) ) )
         => r2_yellow_0(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_yellow_0)).

fof(f4069,plain,
    ( ~ m1_subset_1(sK7(sK2,k4_waybel_0(sK2,sK3),sK3),u1_struct_0(sK2))
    | r2_yellow_0(sK2,sK3) ),
    inference(subsumption_resolution,[],[f4067,f4006])).

fof(f4006,plain,
    ( r1_lattice3(sK2,sK3,sK7(sK2,k4_waybel_0(sK2,sK3),sK3))
    | r2_yellow_0(sK2,sK3) ),
    inference(duplicate_literal_removal,[],[f4005])).

fof(f4005,plain,
    ( r1_lattice3(sK2,sK3,sK7(sK2,k4_waybel_0(sK2,sK3),sK3))
    | r2_yellow_0(sK2,sK3)
    | r2_yellow_0(sK2,sK3) ),
    inference(factoring,[],[f3951])).

fof(f3951,plain,(
    ! [X0] :
      ( r1_lattice3(sK2,X0,sK7(sK2,k4_waybel_0(sK2,sK3),X0))
      | r1_lattice3(sK2,sK3,sK7(sK2,k4_waybel_0(sK2,sK3),X0))
      | r2_yellow_0(sK2,X0)
      | r2_yellow_0(sK2,sK3) ) ),
    inference(resolution,[],[f3807,f3308])).

fof(f3308,plain,
    ( r2_yellow_0(sK2,k4_waybel_0(sK2,sK3))
    | r2_yellow_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f3277])).

fof(f3807,plain,(
    ! [X0] :
      ( ~ r2_yellow_0(sK2,k4_waybel_0(sK2,sK3))
      | r1_lattice3(sK2,X0,sK7(sK2,k4_waybel_0(sK2,sK3),X0))
      | r1_lattice3(sK2,sK3,sK7(sK2,k4_waybel_0(sK2,sK3),X0))
      | r2_yellow_0(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f3806,f3309])).

fof(f3806,plain,(
    ! [X0] :
      ( r2_yellow_0(sK2,X0)
      | r2_yellow_0(sK2,sK3)
      | r1_lattice3(sK2,X0,sK7(sK2,k4_waybel_0(sK2,sK3),X0))
      | r1_lattice3(sK2,sK3,sK7(sK2,k4_waybel_0(sK2,sK3),X0))
      | ~ r2_yellow_0(sK2,k4_waybel_0(sK2,sK3)) ) ),
    inference(subsumption_resolution,[],[f3805,f3303])).

fof(f3805,plain,(
    ! [X0] :
      ( r2_yellow_0(sK2,X0)
      | r2_yellow_0(sK2,sK3)
      | r1_lattice3(sK2,X0,sK7(sK2,k4_waybel_0(sK2,sK3),X0))
      | r1_lattice3(sK2,sK3,sK7(sK2,k4_waybel_0(sK2,sK3),X0))
      | ~ r2_yellow_0(sK2,k4_waybel_0(sK2,sK3))
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f3804,f3306])).

fof(f3804,plain,(
    ! [X0] :
      ( r2_yellow_0(sK2,X0)
      | r2_yellow_0(sK2,sK3)
      | r1_lattice3(sK2,X0,sK7(sK2,k4_waybel_0(sK2,sK3),X0))
      | r1_lattice3(sK2,sK3,sK7(sK2,k4_waybel_0(sK2,sK3),X0))
      | ~ r2_yellow_0(sK2,k4_waybel_0(sK2,sK3))
      | ~ l1_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(duplicate_literal_removal,[],[f3803])).

fof(f3803,plain,(
    ! [X0] :
      ( r2_yellow_0(sK2,X0)
      | r2_yellow_0(sK2,sK3)
      | r1_lattice3(sK2,X0,sK7(sK2,k4_waybel_0(sK2,sK3),X0))
      | r1_lattice3(sK2,sK3,sK7(sK2,k4_waybel_0(sK2,sK3),X0))
      | ~ r2_yellow_0(sK2,k4_waybel_0(sK2,sK3))
      | r2_yellow_0(sK2,X0)
      | ~ l1_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f3589,f3328])).

fof(f3589,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK7(sK2,k4_waybel_0(sK2,sK3),X1),u1_struct_0(sK2))
      | r2_yellow_0(sK2,X1)
      | r2_yellow_0(sK2,sK3)
      | r1_lattice3(sK2,X1,sK7(sK2,k4_waybel_0(sK2,sK3),X1))
      | r1_lattice3(sK2,sK3,sK7(sK2,k4_waybel_0(sK2,sK3),X1)) ) ),
    inference(resolution,[],[f3390,f3436])).

fof(f3436,plain,(
    ! [X2] :
      ( ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK2))
      | r1_lattice3(sK2,sK3,X2) ) ),
    inference(resolution,[],[f3422,f3307])).

fof(f3307,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f3277])).

fof(f3422,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ r1_lattice3(sK2,k4_waybel_0(sK2,X0),X1)
      | r1_lattice3(sK2,X0,X1) ) ),
    inference(subsumption_resolution,[],[f3421,f3303])).

fof(f3421,plain,(
    ! [X0,X1] :
      ( ~ r1_lattice3(sK2,k4_waybel_0(sK2,X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | r1_lattice3(sK2,X0,X1)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f3420,f3304])).

fof(f3304,plain,(
    v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f3277])).

fof(f3420,plain,(
    ! [X0,X1] :
      ( ~ r1_lattice3(sK2,k4_waybel_0(sK2,X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | r1_lattice3(sK2,X0,X1)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f3419,f3306])).

fof(f3419,plain,(
    ! [X0,X1] :
      ( ~ r1_lattice3(sK2,k4_waybel_0(sK2,X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_orders_2(sK2)
      | r1_lattice3(sK2,X0,X1)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f3314,f3305])).

fof(f3305,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f3277])).

fof(f3314,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_orders_2(X0)
      | ~ r1_lattice3(X0,k4_waybel_0(X0,X1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | r1_lattice3(X0,X1,X2)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3278])).

fof(f3278,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_lattice3(X0,X1,X2)
                  | ~ r1_lattice3(X0,k4_waybel_0(X0,X1),X2) )
                & ( r1_lattice3(X0,k4_waybel_0(X0,X1),X2)
                  | ~ r1_lattice3(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3256])).

fof(f3256,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattice3(X0,X1,X2)
              <=> r1_lattice3(X0,k4_waybel_0(X0,X1),X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3255])).

fof(f3255,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattice3(X0,X1,X2)
              <=> r1_lattice3(X0,k4_waybel_0(X0,X1),X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3229])).

fof(f3229,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_lattice3(X0,X1,X2)
              <=> r1_lattice3(X0,k4_waybel_0(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_waybel_0)).

fof(f3390,plain,(
    ! [X0] :
      ( r1_lattice3(sK2,X0,sK7(sK2,k4_waybel_0(sK2,sK3),X0))
      | r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK7(sK2,k4_waybel_0(sK2,sK3),X0))
      | r2_yellow_0(sK2,X0)
      | r2_yellow_0(sK2,sK3) ) ),
    inference(resolution,[],[f3389,f3308])).

fof(f3389,plain,(
    ! [X0,X1] :
      ( ~ r2_yellow_0(sK2,X0)
      | r1_lattice3(sK2,X1,sK7(sK2,X0,X1))
      | r1_lattice3(sK2,X0,sK7(sK2,X0,X1))
      | r2_yellow_0(sK2,X1) ) ),
    inference(subsumption_resolution,[],[f3387,f3303])).

fof(f3387,plain,(
    ! [X0,X1] :
      ( ~ r2_yellow_0(sK2,X0)
      | r1_lattice3(sK2,X1,sK7(sK2,X0,X1))
      | r1_lattice3(sK2,X0,sK7(sK2,X0,X1))
      | r2_yellow_0(sK2,X1)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f3329,f3306])).

fof(f3329,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_yellow_0(X0,X1)
      | r1_lattice3(X0,X2,sK7(X0,X1,X2))
      | r1_lattice3(X0,X1,sK7(X0,X1,X2))
      | r2_yellow_0(X0,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3290])).

fof(f4067,plain,
    ( r2_yellow_0(sK2,sK3)
    | ~ r1_lattice3(sK2,sK3,sK7(sK2,k4_waybel_0(sK2,sK3),sK3))
    | ~ m1_subset_1(sK7(sK2,k4_waybel_0(sK2,sK3),sK3),u1_struct_0(sK2)) ),
    inference(resolution,[],[f4054,f3416])).

fof(f3416,plain,(
    ! [X2] :
      ( r1_lattice3(sK2,k4_waybel_0(sK2,sK3),X2)
      | ~ r1_lattice3(sK2,sK3,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK2)) ) ),
    inference(resolution,[],[f3414,f3307])).

fof(f3414,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ r1_lattice3(sK2,X0,X1)
      | r1_lattice3(sK2,k4_waybel_0(sK2,X0),X1) ) ),
    inference(subsumption_resolution,[],[f3413,f3303])).

fof(f3413,plain,(
    ! [X0,X1] :
      ( ~ r1_lattice3(sK2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | r1_lattice3(sK2,k4_waybel_0(sK2,X0),X1)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f3412,f3304])).

fof(f3412,plain,(
    ! [X0,X1] :
      ( ~ r1_lattice3(sK2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | r1_lattice3(sK2,k4_waybel_0(sK2,X0),X1)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f3411,f3306])).

fof(f3411,plain,(
    ! [X0,X1] :
      ( ~ r1_lattice3(sK2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_orders_2(sK2)
      | r1_lattice3(sK2,k4_waybel_0(sK2,X0),X1)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f3313,f3305])).

fof(f3313,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_orders_2(X0)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | r1_lattice3(X0,k4_waybel_0(X0,X1),X2)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3278])).

fof(f4054,plain,
    ( ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK7(sK2,k4_waybel_0(sK2,sK3),sK3))
    | r2_yellow_0(sK2,sK3) ),
    inference(resolution,[],[f4038,f3308])).

fof(f4038,plain,
    ( ~ r2_yellow_0(sK2,k4_waybel_0(sK2,sK3))
    | ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK7(sK2,k4_waybel_0(sK2,sK3),sK3)) ),
    inference(subsumption_resolution,[],[f4037,f3309])).

fof(f4037,plain,
    ( r2_yellow_0(sK2,sK3)
    | ~ r2_yellow_0(sK2,k4_waybel_0(sK2,sK3))
    | ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK7(sK2,k4_waybel_0(sK2,sK3),sK3)) ),
    inference(subsumption_resolution,[],[f4036,f3303])).

fof(f4036,plain,
    ( r2_yellow_0(sK2,sK3)
    | ~ r2_yellow_0(sK2,k4_waybel_0(sK2,sK3))
    | ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK7(sK2,k4_waybel_0(sK2,sK3),sK3))
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f4035,f3306])).

fof(f4035,plain,
    ( r2_yellow_0(sK2,sK3)
    | ~ r2_yellow_0(sK2,k4_waybel_0(sK2,sK3))
    | ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK7(sK2,k4_waybel_0(sK2,sK3),sK3))
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(duplicate_literal_removal,[],[f4022])).

fof(f4022,plain,
    ( r2_yellow_0(sK2,sK3)
    | ~ r2_yellow_0(sK2,k4_waybel_0(sK2,sK3))
    | r2_yellow_0(sK2,sK3)
    | ~ r1_lattice3(sK2,k4_waybel_0(sK2,sK3),sK7(sK2,k4_waybel_0(sK2,sK3),sK3))
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f4006,f3330])).

fof(f3330,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(X0,X2,sK7(X0,X1,X2))
      | ~ r2_yellow_0(X0,X1)
      | r2_yellow_0(X0,X2)
      | ~ r1_lattice3(X0,X1,sK7(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3290])).

fof(f4147,plain,
    ( r1_lattice3(sK2,sK3,sK7(sK2,sK3,k4_waybel_0(sK2,sK3)))
    | r2_yellow_0(sK2,k4_waybel_0(sK2,sK3))
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f4146,f4082])).

fof(f4082,plain,(
    r2_yellow_0(sK2,sK3) ),
    inference(subsumption_resolution,[],[f3308,f4080])).

fof(f4146,plain,
    ( r1_lattice3(sK2,sK3,sK7(sK2,sK3,k4_waybel_0(sK2,sK3)))
    | ~ r2_yellow_0(sK2,sK3)
    | r2_yellow_0(sK2,k4_waybel_0(sK2,sK3))
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f4143,f3328])).

fof(f4143,plain,
    ( ~ m1_subset_1(sK7(sK2,sK3,k4_waybel_0(sK2,sK3)),u1_struct_0(sK2))
    | r1_lattice3(sK2,sK3,sK7(sK2,sK3,k4_waybel_0(sK2,sK3))) ),
    inference(subsumption_resolution,[],[f4136,f4080])).

fof(f4136,plain,
    ( r1_lattice3(sK2,sK3,sK7(sK2,sK3,k4_waybel_0(sK2,sK3)))
    | r2_yellow_0(sK2,k4_waybel_0(sK2,sK3))
    | ~ m1_subset_1(sK7(sK2,sK3,k4_waybel_0(sK2,sK3)),u1_struct_0(sK2)) ),
    inference(duplicate_literal_removal,[],[f4091])).

fof(f4091,plain,
    ( r1_lattice3(sK2,sK3,sK7(sK2,sK3,k4_waybel_0(sK2,sK3)))
    | r2_yellow_0(sK2,k4_waybel_0(sK2,sK3))
    | ~ m1_subset_1(sK7(sK2,sK3,k4_waybel_0(sK2,sK3)),u1_struct_0(sK2))
    | r1_lattice3(sK2,sK3,sK7(sK2,sK3,k4_waybel_0(sK2,sK3))) ),
    inference(resolution,[],[f4087,f3436])).

fof(f4087,plain,(
    ! [X2] :
      ( r1_lattice3(sK2,X2,sK7(sK2,sK3,X2))
      | r1_lattice3(sK2,sK3,sK7(sK2,sK3,X2))
      | r2_yellow_0(sK2,X2) ) ),
    inference(resolution,[],[f4082,f3389])).

fof(f4396,plain,(
    ~ r1_lattice3(sK2,sK3,sK7(sK2,sK3,k4_waybel_0(sK2,sK3))) ),
    inference(duplicate_literal_removal,[],[f4394])).

fof(f4394,plain,
    ( ~ r1_lattice3(sK2,sK3,sK7(sK2,sK3,k4_waybel_0(sK2,sK3)))
    | ~ r1_lattice3(sK2,sK3,sK7(sK2,sK3,k4_waybel_0(sK2,sK3))) ),
    inference(resolution,[],[f4215,f4082])).

fof(f4215,plain,(
    ! [X0] :
      ( ~ r2_yellow_0(sK2,X0)
      | ~ r1_lattice3(sK2,sK3,sK7(sK2,X0,k4_waybel_0(sK2,sK3)))
      | ~ r1_lattice3(sK2,X0,sK7(sK2,X0,k4_waybel_0(sK2,sK3))) ) ),
    inference(subsumption_resolution,[],[f4214,f3303])).

fof(f4214,plain,(
    ! [X0] :
      ( ~ r1_lattice3(sK2,sK3,sK7(sK2,X0,k4_waybel_0(sK2,sK3)))
      | ~ r2_yellow_0(sK2,X0)
      | ~ r1_lattice3(sK2,X0,sK7(sK2,X0,k4_waybel_0(sK2,sK3)))
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f4213,f3306])).

fof(f4213,plain,(
    ! [X0] :
      ( ~ r1_lattice3(sK2,sK3,sK7(sK2,X0,k4_waybel_0(sK2,sK3)))
      | ~ r2_yellow_0(sK2,X0)
      | ~ r1_lattice3(sK2,X0,sK7(sK2,X0,k4_waybel_0(sK2,sK3)))
      | ~ l1_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f4212,f4080])).

fof(f4212,plain,(
    ! [X0] :
      ( ~ r1_lattice3(sK2,sK3,sK7(sK2,X0,k4_waybel_0(sK2,sK3)))
      | ~ r2_yellow_0(sK2,X0)
      | ~ r1_lattice3(sK2,X0,sK7(sK2,X0,k4_waybel_0(sK2,sK3)))
      | r2_yellow_0(sK2,k4_waybel_0(sK2,sK3))
      | ~ l1_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(duplicate_literal_removal,[],[f4211])).

fof(f4211,plain,(
    ! [X0] :
      ( ~ r1_lattice3(sK2,sK3,sK7(sK2,X0,k4_waybel_0(sK2,sK3)))
      | ~ r2_yellow_0(sK2,X0)
      | ~ r1_lattice3(sK2,X0,sK7(sK2,X0,k4_waybel_0(sK2,sK3)))
      | ~ r2_yellow_0(sK2,X0)
      | r2_yellow_0(sK2,k4_waybel_0(sK2,sK3))
      | ~ l1_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f4081,f3328])).

fof(f4081,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK7(sK2,X0,k4_waybel_0(sK2,sK3)),u1_struct_0(sK2))
      | ~ r1_lattice3(sK2,sK3,sK7(sK2,X0,k4_waybel_0(sK2,sK3)))
      | ~ r2_yellow_0(sK2,X0)
      | ~ r1_lattice3(sK2,X0,sK7(sK2,X0,k4_waybel_0(sK2,sK3))) ) ),
    inference(subsumption_resolution,[],[f3430,f4080])).

fof(f3430,plain,(
    ! [X0] :
      ( ~ r1_lattice3(sK2,sK3,sK7(sK2,X0,k4_waybel_0(sK2,sK3)))
      | ~ m1_subset_1(sK7(sK2,X0,k4_waybel_0(sK2,sK3)),u1_struct_0(sK2))
      | ~ r2_yellow_0(sK2,X0)
      | r2_yellow_0(sK2,k4_waybel_0(sK2,sK3))
      | ~ r1_lattice3(sK2,X0,sK7(sK2,X0,k4_waybel_0(sK2,sK3))) ) ),
    inference(subsumption_resolution,[],[f3429,f3303])).

fof(f3429,plain,(
    ! [X0] :
      ( ~ r1_lattice3(sK2,sK3,sK7(sK2,X0,k4_waybel_0(sK2,sK3)))
      | ~ m1_subset_1(sK7(sK2,X0,k4_waybel_0(sK2,sK3)),u1_struct_0(sK2))
      | ~ r2_yellow_0(sK2,X0)
      | r2_yellow_0(sK2,k4_waybel_0(sK2,sK3))
      | ~ r1_lattice3(sK2,X0,sK7(sK2,X0,k4_waybel_0(sK2,sK3)))
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f3424,f3306])).

fof(f3424,plain,(
    ! [X0] :
      ( ~ r1_lattice3(sK2,sK3,sK7(sK2,X0,k4_waybel_0(sK2,sK3)))
      | ~ m1_subset_1(sK7(sK2,X0,k4_waybel_0(sK2,sK3)),u1_struct_0(sK2))
      | ~ r2_yellow_0(sK2,X0)
      | r2_yellow_0(sK2,k4_waybel_0(sK2,sK3))
      | ~ r1_lattice3(sK2,X0,sK7(sK2,X0,k4_waybel_0(sK2,sK3)))
      | ~ l1_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f3416,f3330])).
%------------------------------------------------------------------------------
