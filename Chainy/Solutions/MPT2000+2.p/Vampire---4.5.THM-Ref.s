%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT2000+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:38 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 579 expanded)
%              Number of leaves         :    9 ( 216 expanded)
%              Depth                    :    8
%              Number of atoms          :  399 (6631 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   21 (   8 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4649,plain,(
    $false ),
    inference(global_subsumption,[],[f4559,f4645])).

fof(f4645,plain,(
    ~ r1_waybel_3(sK8,k12_lattice3(sK8,sK10(sK8,sK9),sK11(sK8,sK9)),sK9) ),
    inference(unit_resulting_resolution,[],[f4406,f4407,f4408,f4409,f4410,f4411,f4412,f4413,f4557,f4560,f4416,f4414,f4415,f4558,f4561,f4446])).

fof(f4446,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ v5_waybel_7(k1_waybel_4(X0),X0)
      | r3_orders_2(X0,X4,X1)
      | ~ r1_waybel_3(X0,k12_lattice3(X0,X4,X5),X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v4_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r3_orders_2(X0,X5,X1)
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f4378])).

fof(f4378,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_waybel_7(X1,X0)
              | ( ~ r3_orders_2(X0,sK18(X0,X1),X1)
                & ~ r3_orders_2(X0,sK17(X0,X1),X1)
                & r1_waybel_3(X0,k12_lattice3(X0,sK17(X0,X1),sK18(X0,X1)),X1)
                & m1_subset_1(sK18(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK17(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r3_orders_2(X0,X5,X1)
                      | r3_orders_2(X0,X4,X1)
                      | ~ r1_waybel_3(X0,k12_lattice3(X0,X4,X5),X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v4_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v5_waybel_7(k1_waybel_4(X0),X0)
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK17,sK18])],[f4375,f4377,f4376])).

fof(f4376,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r3_orders_2(X0,X3,X1)
              & ~ r3_orders_2(X0,X2,X1)
              & r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r3_orders_2(X0,X3,X1)
            & ~ r3_orders_2(X0,sK17(X0,X1),X1)
            & r1_waybel_3(X0,k12_lattice3(X0,sK17(X0,X1),X3),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK17(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f4377,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r3_orders_2(X0,X3,X1)
          & ~ r3_orders_2(X0,sK17(X0,X1),X1)
          & r1_waybel_3(X0,k12_lattice3(X0,sK17(X0,X1),X3),X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r3_orders_2(X0,sK18(X0,X1),X1)
        & ~ r3_orders_2(X0,sK17(X0,X1),X1)
        & r1_waybel_3(X0,k12_lattice3(X0,sK17(X0,X1),sK18(X0,X1)),X1)
        & m1_subset_1(sK18(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f4375,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_waybel_7(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r3_orders_2(X0,X3,X1)
                      & ~ r3_orders_2(X0,X2,X1)
                      & r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r3_orders_2(X0,X5,X1)
                      | r3_orders_2(X0,X4,X1)
                      | ~ r1_waybel_3(X0,k12_lattice3(X0,X4,X5),X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v4_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v5_waybel_7(k1_waybel_4(X0),X0)
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(rectify,[],[f4374])).

fof(f4374,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_waybel_7(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r3_orders_2(X0,X3,X1)
                      & ~ r3_orders_2(X0,X2,X1)
                      & r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( r3_orders_2(X0,X3,X1)
                      | r3_orders_2(X0,X2,X1)
                      | ~ r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v4_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v5_waybel_7(k1_waybel_4(X0),X0)
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f4321])).

fof(f4321,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_waybel_7(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r3_orders_2(X0,X3,X1)
                    | r3_orders_2(X0,X2,X1)
                    | ~ r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v5_waybel_7(k1_waybel_4(X0),X0)
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f4320])).

fof(f4320,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_waybel_7(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r3_orders_2(X0,X3,X1)
                    | r3_orders_2(X0,X2,X1)
                    | ~ r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v5_waybel_7(k1_waybel_4(X0),X0)
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4293])).

fof(f4293,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_waybel_3(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ( v5_waybel_7(k1_waybel_4(X0),X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v4_waybel_7(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ~ ( ~ r3_orders_2(X0,X3,X1)
                          & ~ r3_orders_2(X0,X2,X1)
                          & r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_waybel_7)).

fof(f4561,plain,(
    ~ r3_orders_2(sK8,sK11(sK8,sK9),sK9) ),
    inference(unit_resulting_resolution,[],[f4406,f4407,f4408,f4409,f4410,f4411,f4412,f4413,f4417,f4414,f4415,f4424])).

fof(f4424,plain,(
    ! [X0,X1] :
      ( ~ v5_waybel_7(k1_waybel_4(X0),X0)
      | ~ r3_orders_2(X0,sK11(X0,X1),X1)
      | v5_waybel_6(X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f4359])).

fof(f4359,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v5_waybel_6(X1,X0)
          | ( ~ r3_orders_2(X0,sK11(X0,X1),X1)
            & ~ r3_orders_2(X0,sK10(X0,X1),X1)
            & r1_waybel_3(X0,k12_lattice3(X0,sK10(X0,X1),sK11(X0,X1)),X1)
            & m1_subset_1(sK11(X0,X1),u1_struct_0(X0))
            & m1_subset_1(sK10(X0,X1),u1_struct_0(X0)) )
          | ~ v5_waybel_7(k1_waybel_4(X0),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11])],[f4311,f4358,f4357])).

fof(f4357,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r3_orders_2(X0,X3,X1)
              & ~ r3_orders_2(X0,X2,X1)
              & r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r3_orders_2(X0,X3,X1)
            & ~ r3_orders_2(X0,sK10(X0,X1),X1)
            & r1_waybel_3(X0,k12_lattice3(X0,sK10(X0,X1),X3),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK10(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f4358,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r3_orders_2(X0,X3,X1)
          & ~ r3_orders_2(X0,sK10(X0,X1),X1)
          & r1_waybel_3(X0,k12_lattice3(X0,sK10(X0,X1),X3),X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r3_orders_2(X0,sK11(X0,X1),X1)
        & ~ r3_orders_2(X0,sK10(X0,X1),X1)
        & r1_waybel_3(X0,k12_lattice3(X0,sK10(X0,X1),sK11(X0,X1)),X1)
        & m1_subset_1(sK11(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f4311,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v5_waybel_6(X1,X0)
          | ? [X2] :
              ( ? [X3] :
                  ( ~ r3_orders_2(X0,X3,X1)
                  & ~ r3_orders_2(X0,X2,X1)
                  & r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v5_waybel_7(k1_waybel_4(X0),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f4310])).

fof(f4310,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v5_waybel_6(X1,X0)
          | ? [X2] :
              ( ? [X3] :
                  ( ~ r3_orders_2(X0,X3,X1)
                  & ~ r3_orders_2(X0,X2,X1)
                  & r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v5_waybel_7(k1_waybel_4(X0),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4209])).

fof(f4209,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_waybel_3(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ ( ~ v5_waybel_6(X1,X0)
              & ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ~ ( ~ r3_orders_2(X0,X3,X1)
                          & ~ r3_orders_2(X0,X2,X1)
                          & r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1) ) ) )
              & v5_waybel_7(k1_waybel_4(X0),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l57_waybel_7)).

fof(f4417,plain,(
    ~ v5_waybel_6(sK9,sK8) ),
    inference(cnf_transformation,[],[f4356])).

fof(f4356,plain,
    ( ~ v5_waybel_6(sK9,sK8)
    & v4_waybel_7(sK9,sK8)
    & m1_subset_1(sK9,u1_struct_0(sK8))
    & v5_waybel_7(k1_waybel_4(sK8),sK8)
    & l1_orders_2(sK8)
    & v3_waybel_3(sK8)
    & v2_lattice3(sK8)
    & v1_lattice3(sK8)
    & v1_yellow_0(sK8)
    & v5_orders_2(sK8)
    & v4_orders_2(sK8)
    & v3_orders_2(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f4305,f4355,f4354])).

fof(f4354,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v5_waybel_6(X1,X0)
            & v4_waybel_7(X1,X0)
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & v5_waybel_7(k1_waybel_4(X0),X0)
        & l1_orders_2(X0)
        & v3_waybel_3(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ~ v5_waybel_6(X1,sK8)
          & v4_waybel_7(X1,sK8)
          & m1_subset_1(X1,u1_struct_0(sK8)) )
      & v5_waybel_7(k1_waybel_4(sK8),sK8)
      & l1_orders_2(sK8)
      & v3_waybel_3(sK8)
      & v2_lattice3(sK8)
      & v1_lattice3(sK8)
      & v1_yellow_0(sK8)
      & v5_orders_2(sK8)
      & v4_orders_2(sK8)
      & v3_orders_2(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f4355,plain,
    ( ? [X1] :
        ( ~ v5_waybel_6(X1,sK8)
        & v4_waybel_7(X1,sK8)
        & m1_subset_1(X1,u1_struct_0(sK8)) )
   => ( ~ v5_waybel_6(sK9,sK8)
      & v4_waybel_7(sK9,sK8)
      & m1_subset_1(sK9,u1_struct_0(sK8)) ) ),
    introduced(choice_axiom,[])).

fof(f4305,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v5_waybel_6(X1,X0)
          & v4_waybel_7(X1,X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & v5_waybel_7(k1_waybel_4(X0),X0)
      & l1_orders_2(X0)
      & v3_waybel_3(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f4304])).

fof(f4304,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v5_waybel_6(X1,X0)
          & v4_waybel_7(X1,X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & v5_waybel_7(k1_waybel_4(X0),X0)
      & l1_orders_2(X0)
      & v3_waybel_3(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4295])).

fof(f4295,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_waybel_3(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ( v5_waybel_7(k1_waybel_4(X0),X0)
         => ! [X1] :
              ( m1_subset_1(X1,u1_struct_0(X0))
             => ( v4_waybel_7(X1,X0)
               => v5_waybel_6(X1,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f4294])).

fof(f4294,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_waybel_3(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ( v5_waybel_7(k1_waybel_4(X0),X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v4_waybel_7(X1,X0)
             => v5_waybel_6(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_waybel_7)).

fof(f4558,plain,(
    m1_subset_1(sK11(sK8,sK9),u1_struct_0(sK8)) ),
    inference(unit_resulting_resolution,[],[f4406,f4407,f4408,f4409,f4410,f4411,f4412,f4413,f4417,f4414,f4415,f4421])).

fof(f4421,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK11(X0,X1),u1_struct_0(X0))
      | v5_waybel_6(X1,X0)
      | ~ v5_waybel_7(k1_waybel_4(X0),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f4359])).

fof(f4415,plain,(
    m1_subset_1(sK9,u1_struct_0(sK8)) ),
    inference(cnf_transformation,[],[f4356])).

fof(f4414,plain,(
    v5_waybel_7(k1_waybel_4(sK8),sK8) ),
    inference(cnf_transformation,[],[f4356])).

fof(f4416,plain,(
    v4_waybel_7(sK9,sK8) ),
    inference(cnf_transformation,[],[f4356])).

fof(f4560,plain,(
    ~ r3_orders_2(sK8,sK10(sK8,sK9),sK9) ),
    inference(unit_resulting_resolution,[],[f4406,f4407,f4408,f4409,f4410,f4411,f4412,f4413,f4417,f4414,f4415,f4423])).

fof(f4423,plain,(
    ! [X0,X1] :
      ( ~ v5_waybel_7(k1_waybel_4(X0),X0)
      | ~ r3_orders_2(X0,sK10(X0,X1),X1)
      | v5_waybel_6(X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f4359])).

fof(f4557,plain,(
    m1_subset_1(sK10(sK8,sK9),u1_struct_0(sK8)) ),
    inference(unit_resulting_resolution,[],[f4406,f4407,f4408,f4409,f4410,f4411,f4412,f4413,f4417,f4414,f4415,f4420])).

fof(f4420,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK10(X0,X1),u1_struct_0(X0))
      | v5_waybel_6(X1,X0)
      | ~ v5_waybel_7(k1_waybel_4(X0),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f4359])).

fof(f4413,plain,(
    l1_orders_2(sK8) ),
    inference(cnf_transformation,[],[f4356])).

fof(f4412,plain,(
    v3_waybel_3(sK8) ),
    inference(cnf_transformation,[],[f4356])).

fof(f4411,plain,(
    v2_lattice3(sK8) ),
    inference(cnf_transformation,[],[f4356])).

fof(f4410,plain,(
    v1_lattice3(sK8) ),
    inference(cnf_transformation,[],[f4356])).

fof(f4409,plain,(
    v1_yellow_0(sK8) ),
    inference(cnf_transformation,[],[f4356])).

fof(f4408,plain,(
    v5_orders_2(sK8) ),
    inference(cnf_transformation,[],[f4356])).

fof(f4407,plain,(
    v4_orders_2(sK8) ),
    inference(cnf_transformation,[],[f4356])).

fof(f4406,plain,(
    v3_orders_2(sK8) ),
    inference(cnf_transformation,[],[f4356])).

fof(f4559,plain,(
    r1_waybel_3(sK8,k12_lattice3(sK8,sK10(sK8,sK9),sK11(sK8,sK9)),sK9) ),
    inference(unit_resulting_resolution,[],[f4406,f4407,f4408,f4409,f4410,f4411,f4412,f4413,f4417,f4414,f4415,f4422])).

fof(f4422,plain,(
    ! [X0,X1] :
      ( ~ v5_waybel_7(k1_waybel_4(X0),X0)
      | r1_waybel_3(X0,k12_lattice3(X0,sK10(X0,X1),sK11(X0,X1)),X1)
      | v5_waybel_6(X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f4359])).
%------------------------------------------------------------------------------
