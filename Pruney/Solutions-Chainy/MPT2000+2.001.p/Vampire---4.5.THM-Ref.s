%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:00 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 638 expanded)
%              Number of leaves         :    9 ( 216 expanded)
%              Depth                    :   31
%              Number of atoms          :  833 (7065 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   21 (   8 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1106,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1105,f22])).

fof(f22,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ v5_waybel_6(sK1,sK0)
    & v4_waybel_7(sK1,sK0)
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & v5_waybel_7(k1_waybel_4(sK0),sK0)
    & l1_orders_2(sK0)
    & v3_waybel_3(sK0)
    & v2_lattice3(sK0)
    & v1_lattice3(sK0)
    & v1_yellow_0(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f12,f11])).

fof(f11,plain,
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
          ( ~ v5_waybel_6(X1,sK0)
          & v4_waybel_7(X1,sK0)
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & v5_waybel_7(k1_waybel_4(sK0),sK0)
      & l1_orders_2(sK0)
      & v3_waybel_3(sK0)
      & v2_lattice3(sK0)
      & v1_lattice3(sK0)
      & v1_yellow_0(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ? [X1] :
        ( ~ v5_waybel_6(X1,sK0)
        & v4_waybel_7(X1,sK0)
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ~ v5_waybel_6(sK1,sK0)
      & v4_waybel_7(sK1,sK0)
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
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
    inference(flattening,[],[f5])).

fof(f5,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
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
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_waybel_7)).

fof(f1105,plain,(
    ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f1104,f23])).

fof(f23,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f1104,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f1103,f24])).

fof(f24,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f1103,plain,
    ( ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f1102,f25])).

fof(f25,plain,(
    v1_yellow_0(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f1102,plain,
    ( ~ v1_yellow_0(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f1101,f26])).

fof(f26,plain,(
    v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f1101,plain,
    ( ~ v1_lattice3(sK0)
    | ~ v1_yellow_0(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f1100,f27])).

fof(f27,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f1100,plain,
    ( ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v1_yellow_0(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f1099,f28])).

fof(f28,plain,(
    v3_waybel_3(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f1099,plain,
    ( ~ v3_waybel_3(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v1_yellow_0(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f1098,f29])).

fof(f29,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f1098,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v3_waybel_3(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v1_yellow_0(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f1097,f30])).

fof(f30,plain,(
    v5_waybel_7(k1_waybel_4(sK0),sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f1097,plain,
    ( ~ v5_waybel_7(k1_waybel_4(sK0),sK0)
    | ~ l1_orders_2(sK0)
    | ~ v3_waybel_3(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v1_yellow_0(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f1096,f31])).

fof(f31,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f1096,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v5_waybel_7(k1_waybel_4(sK0),sK0)
    | ~ l1_orders_2(sK0)
    | ~ v3_waybel_3(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v1_yellow_0(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f1095,f32])).

fof(f32,plain,(
    v4_waybel_7(sK1,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f1095,plain,
    ( ~ v4_waybel_7(sK1,sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v5_waybel_7(k1_waybel_4(sK0),sK0)
    | ~ l1_orders_2(sK0)
    | ~ v3_waybel_3(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v1_yellow_0(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f1094,f552])).

fof(f552,plain,(
    m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) ),
    inference(global_subsumption,[],[f31,f30,f551])).

fof(f551,plain,
    ( m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | ~ v5_waybel_7(k1_waybel_4(sK0),sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f550,f22])).

fof(f550,plain,
    ( m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | ~ v5_waybel_7(k1_waybel_4(sK0),sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f549,f23])).

fof(f549,plain,
    ( m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | ~ v5_waybel_7(k1_waybel_4(sK0),sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f548,f24])).

fof(f548,plain,
    ( m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | ~ v5_waybel_7(k1_waybel_4(sK0),sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f547,f25])).

fof(f547,plain,
    ( m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | ~ v5_waybel_7(k1_waybel_4(sK0),sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v1_yellow_0(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f546,f26])).

fof(f546,plain,
    ( m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | ~ v5_waybel_7(k1_waybel_4(sK0),sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v1_lattice3(sK0)
    | ~ v1_yellow_0(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f545,f27])).

fof(f545,plain,
    ( m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | ~ v5_waybel_7(k1_waybel_4(sK0),sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v1_yellow_0(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f544,f28])).

fof(f544,plain,
    ( m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | ~ v5_waybel_7(k1_waybel_4(sK0),sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v3_waybel_3(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v1_yellow_0(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f539,f29])).

fof(f539,plain,
    ( m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | ~ v5_waybel_7(k1_waybel_4(sK0),sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_waybel_3(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v1_yellow_0(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(resolution,[],[f33,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v5_waybel_6(X1,X0)
      | m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
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
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v5_waybel_6(X1,X0)
          | ( ~ r3_orders_2(X0,sK5(X0,X1),X1)
            & ~ r3_orders_2(X0,sK4(X0,X1),X1)
            & r1_waybel_3(X0,k12_lattice3(X0,sK4(X0,X1),sK5(X0,X1)),X1)
            & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
            & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f10,f20,f19])).

fof(f19,plain,(
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
            & ~ r3_orders_2(X0,sK4(X0,X1),X1)
            & r1_waybel_3(X0,k12_lattice3(X0,sK4(X0,X1),X3),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r3_orders_2(X0,X3,X1)
          & ~ r3_orders_2(X0,sK4(X0,X1),X1)
          & r1_waybel_3(X0,k12_lattice3(X0,sK4(X0,X1),X3),X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r3_orders_2(X0,sK5(X0,X1),X1)
        & ~ r3_orders_2(X0,sK4(X0,X1),X1)
        & r1_waybel_3(X0,k12_lattice3(X0,sK4(X0,X1),sK5(X0,X1)),X1)
        & m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

fof(f9,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l57_waybel_7)).

fof(f33,plain,(
    ~ v5_waybel_6(sK1,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f1094,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | ~ v4_waybel_7(sK1,sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v5_waybel_7(k1_waybel_4(sK0),sK0)
    | ~ l1_orders_2(sK0)
    | ~ v3_waybel_3(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v1_yellow_0(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f1093,f561])).

fof(f561,plain,(
    m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0)) ),
    inference(global_subsumption,[],[f31,f30,f560])).

fof(f560,plain,
    ( m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ v5_waybel_7(k1_waybel_4(sK0),sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f559,f22])).

fof(f559,plain,
    ( m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ v5_waybel_7(k1_waybel_4(sK0),sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f558,f23])).

fof(f558,plain,
    ( m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ v5_waybel_7(k1_waybel_4(sK0),sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f557,f24])).

fof(f557,plain,
    ( m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ v5_waybel_7(k1_waybel_4(sK0),sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f556,f25])).

fof(f556,plain,
    ( m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ v5_waybel_7(k1_waybel_4(sK0),sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v1_yellow_0(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f555,f26])).

fof(f555,plain,
    ( m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ v5_waybel_7(k1_waybel_4(sK0),sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v1_lattice3(sK0)
    | ~ v1_yellow_0(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f554,f27])).

fof(f554,plain,
    ( m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ v5_waybel_7(k1_waybel_4(sK0),sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v1_yellow_0(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f553,f28])).

fof(f553,plain,
    ( m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ v5_waybel_7(k1_waybel_4(sK0),sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v3_waybel_3(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v1_yellow_0(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f540,f29])).

fof(f540,plain,
    ( m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ v5_waybel_7(k1_waybel_4(sK0),sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_waybel_3(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v1_yellow_0(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(resolution,[],[f33,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v5_waybel_6(X1,X0)
      | m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
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
    inference(cnf_transformation,[],[f21])).

fof(f1093,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | ~ v4_waybel_7(sK1,sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v5_waybel_7(k1_waybel_4(sK0),sK0)
    | ~ l1_orders_2(sK0)
    | ~ v3_waybel_3(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v1_yellow_0(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f1092,f579])).

fof(f579,plain,(
    ~ r3_orders_2(sK0,sK4(sK0,sK1),sK1) ),
    inference(global_subsumption,[],[f31,f30,f578])).

fof(f578,plain,
    ( ~ r3_orders_2(sK0,sK4(sK0,sK1),sK1)
    | ~ v5_waybel_7(k1_waybel_4(sK0),sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f577,f22])).

fof(f577,plain,
    ( ~ r3_orders_2(sK0,sK4(sK0,sK1),sK1)
    | ~ v5_waybel_7(k1_waybel_4(sK0),sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f576,f23])).

fof(f576,plain,
    ( ~ r3_orders_2(sK0,sK4(sK0,sK1),sK1)
    | ~ v5_waybel_7(k1_waybel_4(sK0),sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f575,f24])).

fof(f575,plain,
    ( ~ r3_orders_2(sK0,sK4(sK0,sK1),sK1)
    | ~ v5_waybel_7(k1_waybel_4(sK0),sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f574,f25])).

fof(f574,plain,
    ( ~ r3_orders_2(sK0,sK4(sK0,sK1),sK1)
    | ~ v5_waybel_7(k1_waybel_4(sK0),sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v1_yellow_0(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f573,f26])).

fof(f573,plain,
    ( ~ r3_orders_2(sK0,sK4(sK0,sK1),sK1)
    | ~ v5_waybel_7(k1_waybel_4(sK0),sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v1_lattice3(sK0)
    | ~ v1_yellow_0(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f572,f27])).

fof(f572,plain,
    ( ~ r3_orders_2(sK0,sK4(sK0,sK1),sK1)
    | ~ v5_waybel_7(k1_waybel_4(sK0),sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v1_yellow_0(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f571,f28])).

fof(f571,plain,
    ( ~ r3_orders_2(sK0,sK4(sK0,sK1),sK1)
    | ~ v5_waybel_7(k1_waybel_4(sK0),sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v3_waybel_3(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v1_yellow_0(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f542,f29])).

fof(f542,plain,
    ( ~ r3_orders_2(sK0,sK4(sK0,sK1),sK1)
    | ~ v5_waybel_7(k1_waybel_4(sK0),sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_waybel_3(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v1_yellow_0(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(resolution,[],[f33,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v5_waybel_6(X1,X0)
      | ~ r3_orders_2(X0,sK4(X0,X1),X1)
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
    inference(cnf_transformation,[],[f21])).

fof(f1092,plain,
    ( r3_orders_2(sK0,sK4(sK0,sK1),sK1)
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | ~ v4_waybel_7(sK1,sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v5_waybel_7(k1_waybel_4(sK0),sK0)
    | ~ l1_orders_2(sK0)
    | ~ v3_waybel_3(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v1_yellow_0(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f1091,f588])).

fof(f588,plain,(
    ~ r3_orders_2(sK0,sK5(sK0,sK1),sK1) ),
    inference(global_subsumption,[],[f31,f30,f587])).

fof(f587,plain,
    ( ~ r3_orders_2(sK0,sK5(sK0,sK1),sK1)
    | ~ v5_waybel_7(k1_waybel_4(sK0),sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f586,f22])).

fof(f586,plain,
    ( ~ r3_orders_2(sK0,sK5(sK0,sK1),sK1)
    | ~ v5_waybel_7(k1_waybel_4(sK0),sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f585,f23])).

fof(f585,plain,
    ( ~ r3_orders_2(sK0,sK5(sK0,sK1),sK1)
    | ~ v5_waybel_7(k1_waybel_4(sK0),sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f584,f24])).

fof(f584,plain,
    ( ~ r3_orders_2(sK0,sK5(sK0,sK1),sK1)
    | ~ v5_waybel_7(k1_waybel_4(sK0),sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f583,f25])).

fof(f583,plain,
    ( ~ r3_orders_2(sK0,sK5(sK0,sK1),sK1)
    | ~ v5_waybel_7(k1_waybel_4(sK0),sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v1_yellow_0(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f582,f26])).

fof(f582,plain,
    ( ~ r3_orders_2(sK0,sK5(sK0,sK1),sK1)
    | ~ v5_waybel_7(k1_waybel_4(sK0),sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v1_lattice3(sK0)
    | ~ v1_yellow_0(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f581,f27])).

fof(f581,plain,
    ( ~ r3_orders_2(sK0,sK5(sK0,sK1),sK1)
    | ~ v5_waybel_7(k1_waybel_4(sK0),sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v1_yellow_0(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f580,f28])).

fof(f580,plain,
    ( ~ r3_orders_2(sK0,sK5(sK0,sK1),sK1)
    | ~ v5_waybel_7(k1_waybel_4(sK0),sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v3_waybel_3(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v1_yellow_0(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f543,f29])).

fof(f543,plain,
    ( ~ r3_orders_2(sK0,sK5(sK0,sK1),sK1)
    | ~ v5_waybel_7(k1_waybel_4(sK0),sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_waybel_3(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v1_yellow_0(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(resolution,[],[f33,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v5_waybel_6(X1,X0)
      | ~ r3_orders_2(X0,sK5(X0,X1),X1)
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
    inference(cnf_transformation,[],[f21])).

fof(f1091,plain,
    ( r3_orders_2(sK0,sK5(sK0,sK1),sK1)
    | r3_orders_2(sK0,sK4(sK0,sK1),sK1)
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | ~ v4_waybel_7(sK1,sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v5_waybel_7(k1_waybel_4(sK0),sK0)
    | ~ l1_orders_2(sK0)
    | ~ v3_waybel_3(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v1_yellow_0(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(resolution,[],[f570,f34])).

fof(f34,plain,(
    ! [X4,X0,X5,X1] :
      ( r3_orders_2(X0,X5,X1)
      | r3_orders_2(X0,X4,X1)
      | ~ r1_waybel_3(X0,k12_lattice3(X0,X4,X5),X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v4_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_waybel_7(k1_waybel_4(X0),X0)
      | ~ l1_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_waybel_7(X1,X0)
              | ( ~ r3_orders_2(X0,sK3(X0,X1),X1)
                & ~ r3_orders_2(X0,sK2(X0,X1),X1)
                & r1_waybel_3(X0,k12_lattice3(X0,sK2(X0,X1),sK3(X0,X1)),X1)
                & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f15,f17,f16])).

fof(f16,plain,(
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
            & ~ r3_orders_2(X0,sK2(X0,X1),X1)
            & r1_waybel_3(X0,k12_lattice3(X0,sK2(X0,X1),X3),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r3_orders_2(X0,X3,X1)
          & ~ r3_orders_2(X0,sK2(X0,X1),X1)
          & r1_waybel_3(X0,k12_lattice3(X0,sK2(X0,X1),X3),X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r3_orders_2(X0,sK3(X0,X1),X1)
        & ~ r3_orders_2(X0,sK2(X0,X1),X1)
        & r1_waybel_3(X0,k12_lattice3(X0,sK2(X0,X1),sK3(X0,X1)),X1)
        & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
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
    inference(rectify,[],[f14])).

fof(f14,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
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
    inference(flattening,[],[f7])).

% (23939)dis+1_14_awrs=converge:awrsf=256:av=off:bs=on:bsr=on:bce=on:cond=fast:gsp=input_only:gs=on:lcm=predicate:lma=on:nm=4:nwc=1.7:sp=weighted_frequency:urr=on_33 on theBenchmark
fof(f7,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_waybel_7)).

fof(f570,plain,(
    r1_waybel_3(sK0,k12_lattice3(sK0,sK4(sK0,sK1),sK5(sK0,sK1)),sK1) ),
    inference(global_subsumption,[],[f31,f30,f569])).

fof(f569,plain,
    ( r1_waybel_3(sK0,k12_lattice3(sK0,sK4(sK0,sK1),sK5(sK0,sK1)),sK1)
    | ~ v5_waybel_7(k1_waybel_4(sK0),sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f568,f22])).

fof(f568,plain,
    ( r1_waybel_3(sK0,k12_lattice3(sK0,sK4(sK0,sK1),sK5(sK0,sK1)),sK1)
    | ~ v5_waybel_7(k1_waybel_4(sK0),sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f567,f23])).

fof(f567,plain,
    ( r1_waybel_3(sK0,k12_lattice3(sK0,sK4(sK0,sK1),sK5(sK0,sK1)),sK1)
    | ~ v5_waybel_7(k1_waybel_4(sK0),sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f566,f24])).

fof(f566,plain,
    ( r1_waybel_3(sK0,k12_lattice3(sK0,sK4(sK0,sK1),sK5(sK0,sK1)),sK1)
    | ~ v5_waybel_7(k1_waybel_4(sK0),sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f565,f25])).

fof(f565,plain,
    ( r1_waybel_3(sK0,k12_lattice3(sK0,sK4(sK0,sK1),sK5(sK0,sK1)),sK1)
    | ~ v5_waybel_7(k1_waybel_4(sK0),sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v1_yellow_0(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f564,f26])).

fof(f564,plain,
    ( r1_waybel_3(sK0,k12_lattice3(sK0,sK4(sK0,sK1),sK5(sK0,sK1)),sK1)
    | ~ v5_waybel_7(k1_waybel_4(sK0),sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v1_lattice3(sK0)
    | ~ v1_yellow_0(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f563,f27])).

fof(f563,plain,
    ( r1_waybel_3(sK0,k12_lattice3(sK0,sK4(sK0,sK1),sK5(sK0,sK1)),sK1)
    | ~ v5_waybel_7(k1_waybel_4(sK0),sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v1_yellow_0(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f562,f28])).

fof(f562,plain,
    ( r1_waybel_3(sK0,k12_lattice3(sK0,sK4(sK0,sK1),sK5(sK0,sK1)),sK1)
    | ~ v5_waybel_7(k1_waybel_4(sK0),sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v3_waybel_3(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v1_yellow_0(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f541,f29])).

fof(f541,plain,
    ( r1_waybel_3(sK0,k12_lattice3(sK0,sK4(sK0,sK1),sK5(sK0,sK1)),sK1)
    | ~ v5_waybel_7(k1_waybel_4(sK0),sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_waybel_3(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v1_yellow_0(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(resolution,[],[f33,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v5_waybel_6(X1,X0)
      | r1_waybel_3(X0,k12_lattice3(X0,sK4(X0,X1),sK5(X0,X1)),X1)
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
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:15:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.43  % (23930)dis+11_3_awrs=decay:awrsf=256:av=off:gs=on:gsem=on:lcm=reverse:nm=0:nwc=1:sos=all:sp=frequency:updr=off_4 on theBenchmark
% 0.20/0.44  % (23923)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 0.20/0.45  % (23930)Refutation found. Thanks to Tanya!
% 0.20/0.45  % SZS status Theorem for theBenchmark
% 0.20/0.46  % (23928)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.20/0.46  % (23931)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% 0.20/0.46  % (23934)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f1106,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(subsumption_resolution,[],[f1105,f22])).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    v3_orders_2(sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f13])).
% 0.20/0.46  fof(f13,plain,(
% 0.20/0.46    (~v5_waybel_6(sK1,sK0) & v4_waybel_7(sK1,sK0) & m1_subset_1(sK1,u1_struct_0(sK0))) & v5_waybel_7(k1_waybel_4(sK0),sK0) & l1_orders_2(sK0) & v3_waybel_3(sK0) & v2_lattice3(sK0) & v1_lattice3(sK0) & v1_yellow_0(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0)),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f12,f11])).
% 0.20/0.46  fof(f11,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : (~v5_waybel_6(X1,X0) & v4_waybel_7(X1,X0) & m1_subset_1(X1,u1_struct_0(X0))) & v5_waybel_7(k1_waybel_4(X0),X0) & l1_orders_2(X0) & v3_waybel_3(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => (? [X1] : (~v5_waybel_6(X1,sK0) & v4_waybel_7(X1,sK0) & m1_subset_1(X1,u1_struct_0(sK0))) & v5_waybel_7(k1_waybel_4(sK0),sK0) & l1_orders_2(sK0) & v3_waybel_3(sK0) & v2_lattice3(sK0) & v1_lattice3(sK0) & v1_yellow_0(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f12,plain,(
% 0.20/0.46    ? [X1] : (~v5_waybel_6(X1,sK0) & v4_waybel_7(X1,sK0) & m1_subset_1(X1,u1_struct_0(sK0))) => (~v5_waybel_6(sK1,sK0) & v4_waybel_7(sK1,sK0) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f6,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : (~v5_waybel_6(X1,X0) & v4_waybel_7(X1,X0) & m1_subset_1(X1,u1_struct_0(X0))) & v5_waybel_7(k1_waybel_4(X0),X0) & l1_orders_2(X0) & v3_waybel_3(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0))),
% 0.20/0.46    inference(flattening,[],[f5])).
% 0.20/0.46  fof(f5,plain,(
% 0.20/0.46    ? [X0] : ((? [X1] : ((~v5_waybel_6(X1,X0) & v4_waybel_7(X1,X0)) & m1_subset_1(X1,u1_struct_0(X0))) & v5_waybel_7(k1_waybel_4(X0),X0)) & (l1_orders_2(X0) & v3_waybel_3(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f4])).
% 0.20/0.46  fof(f4,negated_conjecture,(
% 0.20/0.46    ~! [X0] : ((l1_orders_2(X0) & v3_waybel_3(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => (v5_waybel_7(k1_waybel_4(X0),X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v4_waybel_7(X1,X0) => v5_waybel_6(X1,X0)))))),
% 0.20/0.46    inference(negated_conjecture,[],[f3])).
% 0.20/0.46  fof(f3,conjecture,(
% 0.20/0.46    ! [X0] : ((l1_orders_2(X0) & v3_waybel_3(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => (v5_waybel_7(k1_waybel_4(X0),X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v4_waybel_7(X1,X0) => v5_waybel_6(X1,X0)))))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_waybel_7)).
% 0.20/0.46  fof(f1105,plain,(
% 0.20/0.46    ~v3_orders_2(sK0)),
% 0.20/0.46    inference(subsumption_resolution,[],[f1104,f23])).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    v4_orders_2(sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f13])).
% 0.20/0.46  fof(f1104,plain,(
% 0.20/0.46    ~v4_orders_2(sK0) | ~v3_orders_2(sK0)),
% 0.20/0.46    inference(subsumption_resolution,[],[f1103,f24])).
% 0.20/0.46  fof(f24,plain,(
% 0.20/0.46    v5_orders_2(sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f13])).
% 0.20/0.46  fof(f1103,plain,(
% 0.20/0.46    ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0)),
% 0.20/0.46    inference(subsumption_resolution,[],[f1102,f25])).
% 0.20/0.46  fof(f25,plain,(
% 0.20/0.46    v1_yellow_0(sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f13])).
% 0.20/0.46  fof(f1102,plain,(
% 0.20/0.46    ~v1_yellow_0(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0)),
% 0.20/0.46    inference(subsumption_resolution,[],[f1101,f26])).
% 0.20/0.46  fof(f26,plain,(
% 0.20/0.46    v1_lattice3(sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f13])).
% 0.20/0.46  fof(f1101,plain,(
% 0.20/0.46    ~v1_lattice3(sK0) | ~v1_yellow_0(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0)),
% 0.20/0.46    inference(subsumption_resolution,[],[f1100,f27])).
% 0.20/0.46  fof(f27,plain,(
% 0.20/0.46    v2_lattice3(sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f13])).
% 0.20/0.46  fof(f1100,plain,(
% 0.20/0.46    ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v1_yellow_0(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0)),
% 0.20/0.46    inference(subsumption_resolution,[],[f1099,f28])).
% 0.20/0.46  fof(f28,plain,(
% 0.20/0.46    v3_waybel_3(sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f13])).
% 0.20/0.46  fof(f1099,plain,(
% 0.20/0.46    ~v3_waybel_3(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v1_yellow_0(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0)),
% 0.20/0.46    inference(subsumption_resolution,[],[f1098,f29])).
% 0.20/0.46  fof(f29,plain,(
% 0.20/0.46    l1_orders_2(sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f13])).
% 0.20/0.46  fof(f1098,plain,(
% 0.20/0.46    ~l1_orders_2(sK0) | ~v3_waybel_3(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v1_yellow_0(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0)),
% 0.20/0.46    inference(subsumption_resolution,[],[f1097,f30])).
% 0.20/0.46  fof(f30,plain,(
% 0.20/0.46    v5_waybel_7(k1_waybel_4(sK0),sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f13])).
% 0.20/0.46  fof(f1097,plain,(
% 0.20/0.46    ~v5_waybel_7(k1_waybel_4(sK0),sK0) | ~l1_orders_2(sK0) | ~v3_waybel_3(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v1_yellow_0(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0)),
% 0.20/0.46    inference(subsumption_resolution,[],[f1096,f31])).
% 0.20/0.46  fof(f31,plain,(
% 0.20/0.46    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.46    inference(cnf_transformation,[],[f13])).
% 0.20/0.46  fof(f1096,plain,(
% 0.20/0.46    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v5_waybel_7(k1_waybel_4(sK0),sK0) | ~l1_orders_2(sK0) | ~v3_waybel_3(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v1_yellow_0(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0)),
% 0.20/0.46    inference(subsumption_resolution,[],[f1095,f32])).
% 0.20/0.46  fof(f32,plain,(
% 0.20/0.46    v4_waybel_7(sK1,sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f13])).
% 0.20/0.46  fof(f1095,plain,(
% 0.20/0.46    ~v4_waybel_7(sK1,sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v5_waybel_7(k1_waybel_4(sK0),sK0) | ~l1_orders_2(sK0) | ~v3_waybel_3(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v1_yellow_0(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0)),
% 0.20/0.46    inference(subsumption_resolution,[],[f1094,f552])).
% 0.20/0.46  fof(f552,plain,(
% 0.20/0.46    m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))),
% 0.20/0.46    inference(global_subsumption,[],[f31,f30,f551])).
% 0.20/0.46  fof(f551,plain,(
% 0.20/0.46    m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) | ~v5_waybel_7(k1_waybel_4(sK0),sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.46    inference(subsumption_resolution,[],[f550,f22])).
% 0.20/0.46  fof(f550,plain,(
% 0.20/0.46    m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) | ~v5_waybel_7(k1_waybel_4(sK0),sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v3_orders_2(sK0)),
% 0.20/0.46    inference(subsumption_resolution,[],[f549,f23])).
% 0.20/0.46  fof(f549,plain,(
% 0.20/0.46    m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) | ~v5_waybel_7(k1_waybel_4(sK0),sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0)),
% 0.20/0.46    inference(subsumption_resolution,[],[f548,f24])).
% 0.20/0.46  fof(f548,plain,(
% 0.20/0.46    m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) | ~v5_waybel_7(k1_waybel_4(sK0),sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0)),
% 0.20/0.46    inference(subsumption_resolution,[],[f547,f25])).
% 0.20/0.46  fof(f547,plain,(
% 0.20/0.46    m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) | ~v5_waybel_7(k1_waybel_4(sK0),sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v1_yellow_0(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0)),
% 0.20/0.46    inference(subsumption_resolution,[],[f546,f26])).
% 0.20/0.46  fof(f546,plain,(
% 0.20/0.46    m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) | ~v5_waybel_7(k1_waybel_4(sK0),sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v1_lattice3(sK0) | ~v1_yellow_0(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0)),
% 0.20/0.46    inference(subsumption_resolution,[],[f545,f27])).
% 0.20/0.46  fof(f545,plain,(
% 0.20/0.46    m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) | ~v5_waybel_7(k1_waybel_4(sK0),sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v1_yellow_0(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0)),
% 0.20/0.46    inference(subsumption_resolution,[],[f544,f28])).
% 0.20/0.46  fof(f544,plain,(
% 0.20/0.46    m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) | ~v5_waybel_7(k1_waybel_4(sK0),sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v3_waybel_3(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v1_yellow_0(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0)),
% 0.20/0.46    inference(subsumption_resolution,[],[f539,f29])).
% 0.20/0.46  fof(f539,plain,(
% 0.20/0.46    m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) | ~v5_waybel_7(k1_waybel_4(sK0),sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v3_waybel_3(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v1_yellow_0(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0)),
% 0.20/0.46    inference(resolution,[],[f33,f40])).
% 0.20/0.46  fof(f40,plain,(
% 0.20/0.46    ( ! [X0,X1] : (v5_waybel_6(X1,X0) | m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) | ~v5_waybel_7(k1_waybel_4(X0),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_waybel_3(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f21])).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (v5_waybel_6(X1,X0) | ((~r3_orders_2(X0,sK5(X0,X1),X1) & ~r3_orders_2(X0,sK4(X0,X1),X1) & r1_waybel_3(X0,k12_lattice3(X0,sK4(X0,X1),sK5(X0,X1)),X1) & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))) & m1_subset_1(sK4(X0,X1),u1_struct_0(X0))) | ~v5_waybel_7(k1_waybel_4(X0),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_waybel_3(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0))),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f10,f20,f19])).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    ! [X1,X0] : (? [X2] : (? [X3] : (~r3_orders_2(X0,X3,X1) & ~r3_orders_2(X0,X2,X1) & r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (~r3_orders_2(X0,X3,X1) & ~r3_orders_2(X0,sK4(X0,X1),X1) & r1_waybel_3(X0,k12_lattice3(X0,sK4(X0,X1),X3),X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK4(X0,X1),u1_struct_0(X0))))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ! [X1,X0] : (? [X3] : (~r3_orders_2(X0,X3,X1) & ~r3_orders_2(X0,sK4(X0,X1),X1) & r1_waybel_3(X0,k12_lattice3(X0,sK4(X0,X1),X3),X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r3_orders_2(X0,sK5(X0,X1),X1) & ~r3_orders_2(X0,sK4(X0,X1),X1) & r1_waybel_3(X0,k12_lattice3(X0,sK4(X0,X1),sK5(X0,X1)),X1) & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f10,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (v5_waybel_6(X1,X0) | ? [X2] : (? [X3] : (~r3_orders_2(X0,X3,X1) & ~r3_orders_2(X0,X2,X1) & r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) | ~v5_waybel_7(k1_waybel_4(X0),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_waybel_3(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0))),
% 0.20/0.47    inference(flattening,[],[f9])).
% 0.20/0.47  fof(f9,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : ((v5_waybel_6(X1,X0) | ? [X2] : (? [X3] : ((~r3_orders_2(X0,X3,X1) & ~r3_orders_2(X0,X2,X1) & r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1)) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) | ~v5_waybel_7(k1_waybel_4(X0),X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_waybel_3(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0] : ((l1_orders_2(X0) & v3_waybel_3(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~(~v5_waybel_6(X1,X0) & ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(~r3_orders_2(X0,X3,X1) & ~r3_orders_2(X0,X2,X1) & r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1)))) & v5_waybel_7(k1_waybel_4(X0),X0))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l57_waybel_7)).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    ~v5_waybel_6(sK1,sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f13])).
% 0.20/0.47  fof(f1094,plain,(
% 0.20/0.47    ~m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) | ~v4_waybel_7(sK1,sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v5_waybel_7(k1_waybel_4(sK0),sK0) | ~l1_orders_2(sK0) | ~v3_waybel_3(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v1_yellow_0(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f1093,f561])).
% 0.20/0.47  fof(f561,plain,(
% 0.20/0.47    m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))),
% 0.20/0.47    inference(global_subsumption,[],[f31,f30,f560])).
% 0.20/0.47  fof(f560,plain,(
% 0.20/0.47    m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0)) | ~v5_waybel_7(k1_waybel_4(sK0),sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.47    inference(subsumption_resolution,[],[f559,f22])).
% 0.20/0.47  fof(f559,plain,(
% 0.20/0.47    m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0)) | ~v5_waybel_7(k1_waybel_4(sK0),sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v3_orders_2(sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f558,f23])).
% 0.20/0.47  fof(f558,plain,(
% 0.20/0.47    m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0)) | ~v5_waybel_7(k1_waybel_4(sK0),sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f557,f24])).
% 0.20/0.47  fof(f557,plain,(
% 0.20/0.47    m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0)) | ~v5_waybel_7(k1_waybel_4(sK0),sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f556,f25])).
% 0.20/0.47  fof(f556,plain,(
% 0.20/0.47    m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0)) | ~v5_waybel_7(k1_waybel_4(sK0),sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v1_yellow_0(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f555,f26])).
% 0.20/0.47  fof(f555,plain,(
% 0.20/0.47    m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0)) | ~v5_waybel_7(k1_waybel_4(sK0),sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v1_lattice3(sK0) | ~v1_yellow_0(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f554,f27])).
% 0.20/0.47  fof(f554,plain,(
% 0.20/0.47    m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0)) | ~v5_waybel_7(k1_waybel_4(sK0),sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v1_yellow_0(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f553,f28])).
% 0.20/0.47  fof(f553,plain,(
% 0.20/0.47    m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0)) | ~v5_waybel_7(k1_waybel_4(sK0),sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v3_waybel_3(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v1_yellow_0(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f540,f29])).
% 0.20/0.47  fof(f540,plain,(
% 0.20/0.47    m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0)) | ~v5_waybel_7(k1_waybel_4(sK0),sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v3_waybel_3(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v1_yellow_0(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0)),
% 0.20/0.47    inference(resolution,[],[f33,f41])).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    ( ! [X0,X1] : (v5_waybel_6(X1,X0) | m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) | ~v5_waybel_7(k1_waybel_4(X0),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_waybel_3(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f21])).
% 0.20/0.47  fof(f1093,plain,(
% 0.20/0.47    ~m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) | ~v4_waybel_7(sK1,sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v5_waybel_7(k1_waybel_4(sK0),sK0) | ~l1_orders_2(sK0) | ~v3_waybel_3(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v1_yellow_0(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f1092,f579])).
% 0.20/0.47  fof(f579,plain,(
% 0.20/0.47    ~r3_orders_2(sK0,sK4(sK0,sK1),sK1)),
% 0.20/0.47    inference(global_subsumption,[],[f31,f30,f578])).
% 0.20/0.47  fof(f578,plain,(
% 0.20/0.47    ~r3_orders_2(sK0,sK4(sK0,sK1),sK1) | ~v5_waybel_7(k1_waybel_4(sK0),sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.47    inference(subsumption_resolution,[],[f577,f22])).
% 0.20/0.47  fof(f577,plain,(
% 0.20/0.47    ~r3_orders_2(sK0,sK4(sK0,sK1),sK1) | ~v5_waybel_7(k1_waybel_4(sK0),sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v3_orders_2(sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f576,f23])).
% 0.20/0.47  fof(f576,plain,(
% 0.20/0.47    ~r3_orders_2(sK0,sK4(sK0,sK1),sK1) | ~v5_waybel_7(k1_waybel_4(sK0),sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f575,f24])).
% 0.20/0.47  fof(f575,plain,(
% 0.20/0.47    ~r3_orders_2(sK0,sK4(sK0,sK1),sK1) | ~v5_waybel_7(k1_waybel_4(sK0),sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f574,f25])).
% 0.20/0.47  fof(f574,plain,(
% 0.20/0.47    ~r3_orders_2(sK0,sK4(sK0,sK1),sK1) | ~v5_waybel_7(k1_waybel_4(sK0),sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v1_yellow_0(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f573,f26])).
% 0.20/0.47  fof(f573,plain,(
% 0.20/0.47    ~r3_orders_2(sK0,sK4(sK0,sK1),sK1) | ~v5_waybel_7(k1_waybel_4(sK0),sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v1_lattice3(sK0) | ~v1_yellow_0(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f572,f27])).
% 0.20/0.47  fof(f572,plain,(
% 0.20/0.47    ~r3_orders_2(sK0,sK4(sK0,sK1),sK1) | ~v5_waybel_7(k1_waybel_4(sK0),sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v1_yellow_0(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f571,f28])).
% 0.20/0.47  fof(f571,plain,(
% 0.20/0.47    ~r3_orders_2(sK0,sK4(sK0,sK1),sK1) | ~v5_waybel_7(k1_waybel_4(sK0),sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v3_waybel_3(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v1_yellow_0(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f542,f29])).
% 0.20/0.47  fof(f542,plain,(
% 0.20/0.47    ~r3_orders_2(sK0,sK4(sK0,sK1),sK1) | ~v5_waybel_7(k1_waybel_4(sK0),sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v3_waybel_3(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v1_yellow_0(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0)),
% 0.20/0.47    inference(resolution,[],[f33,f43])).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    ( ! [X0,X1] : (v5_waybel_6(X1,X0) | ~r3_orders_2(X0,sK4(X0,X1),X1) | ~v5_waybel_7(k1_waybel_4(X0),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_waybel_3(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f21])).
% 0.20/0.47  fof(f1092,plain,(
% 0.20/0.47    r3_orders_2(sK0,sK4(sK0,sK1),sK1) | ~m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) | ~v4_waybel_7(sK1,sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v5_waybel_7(k1_waybel_4(sK0),sK0) | ~l1_orders_2(sK0) | ~v3_waybel_3(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v1_yellow_0(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f1091,f588])).
% 0.20/0.47  fof(f588,plain,(
% 0.20/0.47    ~r3_orders_2(sK0,sK5(sK0,sK1),sK1)),
% 0.20/0.47    inference(global_subsumption,[],[f31,f30,f587])).
% 0.20/0.47  fof(f587,plain,(
% 0.20/0.47    ~r3_orders_2(sK0,sK5(sK0,sK1),sK1) | ~v5_waybel_7(k1_waybel_4(sK0),sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.47    inference(subsumption_resolution,[],[f586,f22])).
% 0.20/0.47  fof(f586,plain,(
% 0.20/0.47    ~r3_orders_2(sK0,sK5(sK0,sK1),sK1) | ~v5_waybel_7(k1_waybel_4(sK0),sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v3_orders_2(sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f585,f23])).
% 0.20/0.47  fof(f585,plain,(
% 0.20/0.47    ~r3_orders_2(sK0,sK5(sK0,sK1),sK1) | ~v5_waybel_7(k1_waybel_4(sK0),sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f584,f24])).
% 0.20/0.47  fof(f584,plain,(
% 0.20/0.47    ~r3_orders_2(sK0,sK5(sK0,sK1),sK1) | ~v5_waybel_7(k1_waybel_4(sK0),sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f583,f25])).
% 0.20/0.47  fof(f583,plain,(
% 0.20/0.47    ~r3_orders_2(sK0,sK5(sK0,sK1),sK1) | ~v5_waybel_7(k1_waybel_4(sK0),sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v1_yellow_0(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f582,f26])).
% 0.20/0.47  fof(f582,plain,(
% 0.20/0.47    ~r3_orders_2(sK0,sK5(sK0,sK1),sK1) | ~v5_waybel_7(k1_waybel_4(sK0),sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v1_lattice3(sK0) | ~v1_yellow_0(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f581,f27])).
% 0.20/0.47  fof(f581,plain,(
% 0.20/0.47    ~r3_orders_2(sK0,sK5(sK0,sK1),sK1) | ~v5_waybel_7(k1_waybel_4(sK0),sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v1_yellow_0(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f580,f28])).
% 0.20/0.47  fof(f580,plain,(
% 0.20/0.47    ~r3_orders_2(sK0,sK5(sK0,sK1),sK1) | ~v5_waybel_7(k1_waybel_4(sK0),sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v3_waybel_3(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v1_yellow_0(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f543,f29])).
% 0.20/0.47  fof(f543,plain,(
% 0.20/0.47    ~r3_orders_2(sK0,sK5(sK0,sK1),sK1) | ~v5_waybel_7(k1_waybel_4(sK0),sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v3_waybel_3(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v1_yellow_0(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0)),
% 0.20/0.47    inference(resolution,[],[f33,f44])).
% 0.20/0.47  fof(f44,plain,(
% 0.20/0.47    ( ! [X0,X1] : (v5_waybel_6(X1,X0) | ~r3_orders_2(X0,sK5(X0,X1),X1) | ~v5_waybel_7(k1_waybel_4(X0),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_waybel_3(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f21])).
% 0.20/0.47  fof(f1091,plain,(
% 0.20/0.47    r3_orders_2(sK0,sK5(sK0,sK1),sK1) | r3_orders_2(sK0,sK4(sK0,sK1),sK1) | ~m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) | ~v4_waybel_7(sK1,sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v5_waybel_7(k1_waybel_4(sK0),sK0) | ~l1_orders_2(sK0) | ~v3_waybel_3(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v1_yellow_0(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0)),
% 0.20/0.47    inference(resolution,[],[f570,f34])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    ( ! [X4,X0,X5,X1] : (r3_orders_2(X0,X5,X1) | r3_orders_2(X0,X4,X1) | ~r1_waybel_3(X0,k12_lattice3(X0,X4,X5),X1) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v4_waybel_7(X1,X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v5_waybel_7(k1_waybel_4(X0),X0) | ~l1_orders_2(X0) | ~v3_waybel_3(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (((v4_waybel_7(X1,X0) | ((~r3_orders_2(X0,sK3(X0,X1),X1) & ~r3_orders_2(X0,sK2(X0,X1),X1) & r1_waybel_3(X0,k12_lattice3(X0,sK2(X0,X1),sK3(X0,X1)),X1) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r3_orders_2(X0,X5,X1) | r3_orders_2(X0,X4,X1) | ~r1_waybel_3(X0,k12_lattice3(X0,X4,X5),X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v4_waybel_7(X1,X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v5_waybel_7(k1_waybel_4(X0),X0) | ~l1_orders_2(X0) | ~v3_waybel_3(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0))),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f15,f17,f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ! [X1,X0] : (? [X2] : (? [X3] : (~r3_orders_2(X0,X3,X1) & ~r3_orders_2(X0,X2,X1) & r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (~r3_orders_2(X0,X3,X1) & ~r3_orders_2(X0,sK2(X0,X1),X1) & r1_waybel_3(X0,k12_lattice3(X0,sK2(X0,X1),X3),X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ! [X1,X0] : (? [X3] : (~r3_orders_2(X0,X3,X1) & ~r3_orders_2(X0,sK2(X0,X1),X1) & r1_waybel_3(X0,k12_lattice3(X0,sK2(X0,X1),X3),X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r3_orders_2(X0,sK3(X0,X1),X1) & ~r3_orders_2(X0,sK2(X0,X1),X1) & r1_waybel_3(X0,k12_lattice3(X0,sK2(X0,X1),sK3(X0,X1)),X1) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (((v4_waybel_7(X1,X0) | ? [X2] : (? [X3] : (~r3_orders_2(X0,X3,X1) & ~r3_orders_2(X0,X2,X1) & r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r3_orders_2(X0,X5,X1) | r3_orders_2(X0,X4,X1) | ~r1_waybel_3(X0,k12_lattice3(X0,X4,X5),X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v4_waybel_7(X1,X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v5_waybel_7(k1_waybel_4(X0),X0) | ~l1_orders_2(X0) | ~v3_waybel_3(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0))),
% 0.20/0.47    inference(rectify,[],[f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (((v4_waybel_7(X1,X0) | ? [X2] : (? [X3] : (~r3_orders_2(X0,X3,X1) & ~r3_orders_2(X0,X2,X1) & r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (! [X3] : (r3_orders_2(X0,X3,X1) | r3_orders_2(X0,X2,X1) | ~r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v4_waybel_7(X1,X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v5_waybel_7(k1_waybel_4(X0),X0) | ~l1_orders_2(X0) | ~v3_waybel_3(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0))),
% 0.20/0.47    inference(nnf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : ((v4_waybel_7(X1,X0) <=> ! [X2] : (! [X3] : (r3_orders_2(X0,X3,X1) | r3_orders_2(X0,X2,X1) | ~r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v5_waybel_7(k1_waybel_4(X0),X0) | ~l1_orders_2(X0) | ~v3_waybel_3(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0))),
% 0.20/0.47    inference(flattening,[],[f7])).
% 0.20/0.47  % (23939)dis+1_14_awrs=converge:awrsf=256:av=off:bs=on:bsr=on:bce=on:cond=fast:gsp=input_only:gs=on:lcm=predicate:lma=on:nm=4:nwc=1.7:sp=weighted_frequency:urr=on_33 on theBenchmark
% 0.20/0.47  fof(f7,plain,(
% 0.20/0.47    ! [X0] : ((! [X1] : ((v4_waybel_7(X1,X0) <=> ! [X2] : (! [X3] : ((r3_orders_2(X0,X3,X1) | r3_orders_2(X0,X2,X1) | ~r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v5_waybel_7(k1_waybel_4(X0),X0)) | (~l1_orders_2(X0) | ~v3_waybel_3(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0] : ((l1_orders_2(X0) & v3_waybel_3(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => (v5_waybel_7(k1_waybel_4(X0),X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v4_waybel_7(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(~r3_orders_2(X0,X3,X1) & ~r3_orders_2(X0,X2,X1) & r1_waybel_3(X0,k12_lattice3(X0,X2,X3),X1))))))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_waybel_7)).
% 0.20/0.47  fof(f570,plain,(
% 0.20/0.47    r1_waybel_3(sK0,k12_lattice3(sK0,sK4(sK0,sK1),sK5(sK0,sK1)),sK1)),
% 0.20/0.47    inference(global_subsumption,[],[f31,f30,f569])).
% 0.20/0.47  fof(f569,plain,(
% 0.20/0.47    r1_waybel_3(sK0,k12_lattice3(sK0,sK4(sK0,sK1),sK5(sK0,sK1)),sK1) | ~v5_waybel_7(k1_waybel_4(sK0),sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.47    inference(subsumption_resolution,[],[f568,f22])).
% 0.20/0.47  fof(f568,plain,(
% 0.20/0.47    r1_waybel_3(sK0,k12_lattice3(sK0,sK4(sK0,sK1),sK5(sK0,sK1)),sK1) | ~v5_waybel_7(k1_waybel_4(sK0),sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v3_orders_2(sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f567,f23])).
% 0.20/0.47  fof(f567,plain,(
% 0.20/0.47    r1_waybel_3(sK0,k12_lattice3(sK0,sK4(sK0,sK1),sK5(sK0,sK1)),sK1) | ~v5_waybel_7(k1_waybel_4(sK0),sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f566,f24])).
% 0.20/0.47  fof(f566,plain,(
% 0.20/0.47    r1_waybel_3(sK0,k12_lattice3(sK0,sK4(sK0,sK1),sK5(sK0,sK1)),sK1) | ~v5_waybel_7(k1_waybel_4(sK0),sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f565,f25])).
% 0.20/0.47  fof(f565,plain,(
% 0.20/0.47    r1_waybel_3(sK0,k12_lattice3(sK0,sK4(sK0,sK1),sK5(sK0,sK1)),sK1) | ~v5_waybel_7(k1_waybel_4(sK0),sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v1_yellow_0(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f564,f26])).
% 0.20/0.47  fof(f564,plain,(
% 0.20/0.47    r1_waybel_3(sK0,k12_lattice3(sK0,sK4(sK0,sK1),sK5(sK0,sK1)),sK1) | ~v5_waybel_7(k1_waybel_4(sK0),sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v1_lattice3(sK0) | ~v1_yellow_0(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f563,f27])).
% 0.20/0.47  fof(f563,plain,(
% 0.20/0.47    r1_waybel_3(sK0,k12_lattice3(sK0,sK4(sK0,sK1),sK5(sK0,sK1)),sK1) | ~v5_waybel_7(k1_waybel_4(sK0),sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v1_yellow_0(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f562,f28])).
% 0.20/0.47  fof(f562,plain,(
% 0.20/0.47    r1_waybel_3(sK0,k12_lattice3(sK0,sK4(sK0,sK1),sK5(sK0,sK1)),sK1) | ~v5_waybel_7(k1_waybel_4(sK0),sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v3_waybel_3(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v1_yellow_0(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f541,f29])).
% 0.20/0.47  fof(f541,plain,(
% 0.20/0.47    r1_waybel_3(sK0,k12_lattice3(sK0,sK4(sK0,sK1),sK5(sK0,sK1)),sK1) | ~v5_waybel_7(k1_waybel_4(sK0),sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v3_waybel_3(sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0) | ~v1_yellow_0(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0)),
% 0.20/0.47    inference(resolution,[],[f33,f42])).
% 0.20/0.47  fof(f42,plain,(
% 0.20/0.47    ( ! [X0,X1] : (v5_waybel_6(X1,X0) | r1_waybel_3(X0,k12_lattice3(X0,sK4(X0,X1),sK5(X0,X1)),X1) | ~v5_waybel_7(k1_waybel_4(X0),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_waybel_3(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f21])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (23930)------------------------------
% 0.20/0.47  % (23930)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (23930)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (23930)Memory used [KB]: 5884
% 0.20/0.47  % (23930)Time elapsed: 0.067 s
% 0.20/0.47  % (23930)------------------------------
% 0.20/0.47  % (23930)------------------------------
% 0.20/0.47  % (23918)Success in time 0.115 s
%------------------------------------------------------------------------------
