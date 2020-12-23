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
% DateTime   : Thu Dec  3 13:15:35 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 343 expanded)
%              Number of leaves         :   15 ( 115 expanded)
%              Depth                    :   36
%              Number of atoms          :  812 (2686 expanded)
%              Number of equality atoms :   67 ( 346 expanded)
%              Maximal formula depth    :   22 (   9 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f458,plain,(
    $false ),
    inference(subsumption_resolution,[],[f457,f46])).

fof(f46,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( sK1 != k12_lattice3(sK0,sK1,k13_lattice3(sK0,sK1,sK2))
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v2_lattice3(sK0)
    & v1_lattice3(sK0)
    & v5_orders_2(sK0)
    & v3_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f34,f33,f32])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k12_lattice3(sK0,X1,k13_lattice3(sK0,X1,X2)) != X1
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v2_lattice3(sK0)
      & v1_lattice3(sK0)
      & v5_orders_2(sK0)
      & v3_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k12_lattice3(sK0,X1,k13_lattice3(sK0,X1,X2)) != X1
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( sK1 != k12_lattice3(sK0,sK1,k13_lattice3(sK0,sK1,X2))
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X2] :
        ( sK1 != k12_lattice3(sK0,sK1,k13_lattice3(sK0,sK1,X2))
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( sK1 != k12_lattice3(sK0,sK1,k13_lattice3(sK0,sK1,sK2))
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_lattice3)).

fof(f457,plain,(
    ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f456,f49])).

fof(f49,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f456,plain,
    ( ~ v2_lattice3(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f455,f47])).

fof(f47,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f455,plain,
    ( ~ v5_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f454,f48])).

fof(f48,plain,(
    v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f454,plain,
    ( ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f453,f50])).

fof(f50,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f453,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f452,f51])).

fof(f51,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f35])).

fof(f452,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(resolution,[],[f451,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( r1_orders_2(X1,X0,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ v2_lattice3(X1)
      | ~ v3_orders_2(X1) ) ),
    inference(condensation,[],[f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v2_lattice3(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f111,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k12_lattice3)).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v2_lattice3(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(superposition,[],[f86,f107])).

fof(f107,plain,(
    ! [X4,X5,X3] :
      ( k10_lattice3(X3,k12_lattice3(X3,X4,X5),X5) = X5
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | ~ v2_lattice3(X3)
      | ~ v1_lattice3(X3)
      | ~ v5_orders_2(X3)
      | ~ v3_orders_2(X3) ) ),
    inference(subsumption_resolution,[],[f106,f72])).

fof(f106,plain,(
    ! [X4,X5,X3] :
      ( k10_lattice3(X3,k12_lattice3(X3,X4,X5),X5) = X5
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | ~ v2_lattice3(X3)
      | ~ v1_lattice3(X3)
      | ~ v5_orders_2(X3)
      | ~ v3_orders_2(X3)
      | ~ m1_subset_1(k12_lattice3(X3,X4,X5),u1_struct_0(X3)) ) ),
    inference(duplicate_literal_removal,[],[f103])).

fof(f103,plain,(
    ! [X4,X5,X3] :
      ( k10_lattice3(X3,k12_lattice3(X3,X4,X5),X5) = X5
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | ~ v2_lattice3(X3)
      | ~ v1_lattice3(X3)
      | ~ v5_orders_2(X3)
      | ~ v3_orders_2(X3)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(k12_lattice3(X3,X4,X5),u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | ~ v1_lattice3(X3)
      | ~ v5_orders_2(X3) ) ),
    inference(superposition,[],[f70,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_lattice3)).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X2,k10_lattice3(X0,X1,X2))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f76,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X2,k10_lattice3(X0,X1,X2))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X2,X3)
      | k10_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k10_lattice3(X0,X1,X2) = X3
                      | ( ~ r1_orders_2(X0,X3,sK3(X0,X1,X2,X3))
                        & r1_orders_2(X0,X2,sK3(X0,X1,X2,X3))
                        & r1_orders_2(X0,X1,sK3(X0,X1,X2,X3))
                        & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X3,X5)
                            | ~ r1_orders_2(X0,X2,X5)
                            | ~ r1_orders_2(X0,X1,X5)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | k10_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f38,f39])).

fof(f39,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X3,X4)
          & r1_orders_2(X0,X2,X4)
          & r1_orders_2(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X3,sK3(X0,X1,X2,X3))
        & r1_orders_2(X0,X2,sK3(X0,X1,X2,X3))
        & r1_orders_2(X0,X1,sK3(X0,X1,X2,X3))
        & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k10_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X3,X4)
                          & r1_orders_2(X0,X2,X4)
                          & r1_orders_2(X0,X1,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X3,X5)
                            | ~ r1_orders_2(X0,X2,X5)
                            | ~ r1_orders_2(X0,X1,X5)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | k10_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k10_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X3,X4)
                          & r1_orders_2(X0,X2,X4)
                          & r1_orders_2(X0,X1,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X3,X4)
                            | ~ r1_orders_2(X0,X2,X4)
                            | ~ r1_orders_2(X0,X1,X4)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | k10_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k10_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X3,X4)
                          & r1_orders_2(X0,X2,X4)
                          & r1_orders_2(X0,X1,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X3,X4)
                            | ~ r1_orders_2(X0,X2,X4)
                            | ~ r1_orders_2(X0,X1,X4)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | k10_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k10_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X3,X4)
                          | ~ r1_orders_2(X0,X2,X4)
                          | ~ r1_orders_2(X0,X1,X4)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k10_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X3,X4)
                          | ~ r1_orders_2(X0,X2,X4)
                          | ~ r1_orders_2(X0,X1,X4)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( k10_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X2,X4)
                              & r1_orders_2(X0,X1,X4) )
                           => r1_orders_2(X0,X3,X4) ) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l26_lattice3)).

fof(f451,plain,(
    ~ r1_orders_2(sK0,sK1,sK1) ),
    inference(subsumption_resolution,[],[f450,f50])).

fof(f450,plain,
    ( ~ r1_orders_2(sK0,sK1,sK1)
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f449,f51])).

fof(f449,plain,
    ( ~ r1_orders_2(sK0,sK1,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f444,f52])).

fof(f52,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f35])).

fof(f444,plain,
    ( ~ r1_orders_2(sK0,sK1,sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f443,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_lattice3)).

fof(f443,plain,
    ( ~ m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,sK1) ),
    inference(subsumption_resolution,[],[f442,f47])).

fof(f442,plain,
    ( ~ r1_orders_2(sK0,sK1,sK1)
    | ~ m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f441,f48])).

fof(f441,plain,
    ( ~ r1_orders_2(sK0,sK1,sK1)
    | ~ m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f440,f50])).

fof(f440,plain,
    ( ~ r1_orders_2(sK0,sK1,sK1)
    | ~ m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f439,f51])).

fof(f439,plain,
    ( ~ r1_orders_2(sK0,sK1,sK1)
    | ~ m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f438,f52])).

fof(f438,plain,
    ( ~ r1_orders_2(sK0,sK1,sK1)
    | ~ m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(duplicate_literal_removal,[],[f433])).

fof(f433,plain,
    ( ~ r1_orders_2(sK0,sK1,sK1)
    | ~ m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(resolution,[],[f414,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f77,f54])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,X3)
      | k10_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f414,plain,
    ( ~ r1_orders_2(sK0,sK1,k10_lattice3(sK0,sK1,sK2))
    | ~ r1_orders_2(sK0,sK1,sK1)
    | ~ m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f413,f47])).

fof(f413,plain,
    ( ~ r1_orders_2(sK0,sK1,k10_lattice3(sK0,sK1,sK2))
    | ~ r1_orders_2(sK0,sK1,sK1)
    | ~ m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f412,f49])).

fof(f412,plain,
    ( ~ r1_orders_2(sK0,sK1,k10_lattice3(sK0,sK1,sK2))
    | ~ r1_orders_2(sK0,sK1,sK1)
    | ~ m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f411,f50])).

fof(f411,plain,
    ( ~ r1_orders_2(sK0,sK1,k10_lattice3(sK0,sK1,sK2))
    | ~ r1_orders_2(sK0,sK1,sK1)
    | ~ m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f409,f51])).

fof(f409,plain,
    ( ~ r1_orders_2(sK0,sK1,k10_lattice3(sK0,sK1,sK2))
    | ~ r1_orders_2(sK0,sK1,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(trivial_inequality_removal,[],[f383])).

fof(f383,plain,
    ( sK1 != sK1
    | ~ r1_orders_2(sK0,sK1,k10_lattice3(sK0,sK1,sK2))
    | ~ r1_orders_2(sK0,sK1,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(superposition,[],[f102,f380])).

fof(f380,plain,(
    ! [X6,X8,X7] :
      ( k12_lattice3(X6,X7,X8) = X7
      | ~ r1_orders_2(X6,X7,X8)
      | ~ r1_orders_2(X6,X7,X7)
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ l1_orders_2(X6)
      | ~ v2_lattice3(X6)
      | ~ v5_orders_2(X6) ) ),
    inference(duplicate_literal_removal,[],[f368])).

fof(f368,plain,(
    ! [X6,X8,X7] :
      ( k12_lattice3(X6,X7,X8) = X7
      | ~ r1_orders_2(X6,X7,X8)
      | ~ r1_orders_2(X6,X7,X7)
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ l1_orders_2(X6)
      | ~ v2_lattice3(X6)
      | ~ v5_orders_2(X6)
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ l1_orders_2(X6)
      | ~ v2_lattice3(X6)
      | ~ v5_orders_2(X6) ) ),
    inference(superposition,[],[f335,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

fof(f335,plain,(
    ! [X2,X0,X1] :
      ( k11_lattice3(X0,X1,X2) = X1
      | ~ r1_orders_2(X0,X1,X2)
      | ~ r1_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f332])).

fof(f332,plain,(
    ! [X2,X0,X1] :
      ( k11_lattice3(X0,X1,X2) = X1
      | ~ r1_orders_2(X0,X1,X2)
      | ~ r1_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | k11_lattice3(X0,X1,X2) = X1
      | ~ r1_orders_2(X0,X1,X2)
      | ~ r1_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(resolution,[],[f90,f88])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,sK4(X0,X1,X2,X3),X3)
      | k11_lattice3(X0,X1,X2) = X3
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f69,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v2_lattice3(X0)
      | ~ v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( k11_lattice3(X0,X1,X2) = X3
      | ~ r1_orders_2(X0,sK4(X0,X1,X2,X3),X3)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k11_lattice3(X0,X1,X2) = X3
                      | ( ~ r1_orders_2(X0,sK4(X0,X1,X2,X3),X3)
                        & r1_orders_2(X0,sK4(X0,X1,X2,X3),X2)
                        & r1_orders_2(X0,sK4(X0,X1,X2,X3),X1)
                        & m1_subset_1(sK4(X0,X1,X2,X3),u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X5,X3)
                            | ~ r1_orders_2(X0,X5,X2)
                            | ~ r1_orders_2(X0,X5,X1)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k11_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f43,f44])).

fof(f44,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X4,X3)
          & r1_orders_2(X0,X4,X2)
          & r1_orders_2(X0,X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK4(X0,X1,X2,X3),X3)
        & r1_orders_2(X0,sK4(X0,X1,X2,X3),X2)
        & r1_orders_2(X0,sK4(X0,X1,X2,X3),X1)
        & m1_subset_1(sK4(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k11_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r1_orders_2(X0,X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X5,X3)
                            | ~ r1_orders_2(X0,X5,X2)
                            | ~ r1_orders_2(X0,X5,X1)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k11_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k11_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r1_orders_2(X0,X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X4,X3)
                            | ~ r1_orders_2(X0,X4,X2)
                            | ~ r1_orders_2(X0,X4,X1)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k11_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k11_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r1_orders_2(X0,X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X4,X3)
                            | ~ r1_orders_2(X0,X4,X2)
                            | ~ r1_orders_2(X0,X4,X1)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k11_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k11_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r1_orders_2(X0,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k11_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r1_orders_2(X0,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( k11_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X4,X2)
                              & r1_orders_2(X0,X4,X1) )
                           => r1_orders_2(X0,X4,X3) ) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l28_lattice3)).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,sK4(X0,X1,X2,X3),X1)
      | k11_lattice3(X0,X1,X2) = X3
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f67,f55])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( k11_lattice3(X0,X1,X2) = X3
      | r1_orders_2(X0,sK4(X0,X1,X2,X3),X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f102,plain,(
    sK1 != k12_lattice3(sK0,sK1,k10_lattice3(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f101,f47])).

fof(f101,plain,
    ( sK1 != k12_lattice3(sK0,sK1,k10_lattice3(sK0,sK1,sK2))
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f100,f48])).

fof(f100,plain,
    ( sK1 != k12_lattice3(sK0,sK1,k10_lattice3(sK0,sK1,sK2))
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f99,f50])).

fof(f99,plain,
    ( sK1 != k12_lattice3(sK0,sK1,k10_lattice3(sK0,sK1,sK2))
    | ~ l1_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f98,f51])).

fof(f98,plain,
    ( sK1 != k12_lattice3(sK0,sK1,k10_lattice3(sK0,sK1,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f97,f52])).

fof(f97,plain,
    ( sK1 != k12_lattice3(sK0,sK1,k10_lattice3(sK0,sK1,sK2))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(superposition,[],[f53,f71])).

fof(f53,plain,(
    sK1 != k12_lattice3(sK0,sK1,k13_lattice3(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:51:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.48  % (8071)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.49  % (8067)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.52  % (8077)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (8069)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.52  % (8084)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.52  % (8083)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.53  % (8085)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.53  % (8066)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.53  % (8085)Refutation not found, incomplete strategy% (8085)------------------------------
% 0.20/0.53  % (8085)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (8085)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (8085)Memory used [KB]: 10618
% 0.20/0.53  % (8085)Time elapsed: 0.093 s
% 0.20/0.53  % (8085)------------------------------
% 0.20/0.53  % (8085)------------------------------
% 0.20/0.53  % (8070)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.54  % (8078)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.54  % (8083)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.55  % SZS output start Proof for theBenchmark
% 0.20/0.55  fof(f458,plain,(
% 0.20/0.55    $false),
% 0.20/0.55    inference(subsumption_resolution,[],[f457,f46])).
% 0.20/0.55  fof(f46,plain,(
% 0.20/0.55    v3_orders_2(sK0)),
% 0.20/0.55    inference(cnf_transformation,[],[f35])).
% 0.20/0.55  fof(f35,plain,(
% 0.20/0.55    ((sK1 != k12_lattice3(sK0,sK1,k13_lattice3(sK0,sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v2_lattice3(sK0) & v1_lattice3(sK0) & v5_orders_2(sK0) & v3_orders_2(sK0)),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f34,f33,f32])).
% 0.20/0.55  fof(f32,plain,(
% 0.20/0.55    ? [X0] : (? [X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => (? [X1] : (? [X2] : (k12_lattice3(sK0,X1,k13_lattice3(sK0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v2_lattice3(sK0) & v1_lattice3(sK0) & v5_orders_2(sK0) & v3_orders_2(sK0))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f33,plain,(
% 0.20/0.55    ? [X1] : (? [X2] : (k12_lattice3(sK0,X1,k13_lattice3(sK0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (sK1 != k12_lattice3(sK0,sK1,k13_lattice3(sK0,sK1,X2)) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f34,plain,(
% 0.20/0.55    ? [X2] : (sK1 != k12_lattice3(sK0,sK1,k13_lattice3(sK0,sK1,X2)) & m1_subset_1(X2,u1_struct_0(sK0))) => (sK1 != k12_lattice3(sK0,sK1,k13_lattice3(sK0,sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f13,plain,(
% 0.20/0.55    ? [X0] : (? [X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0))),
% 0.20/0.55    inference(flattening,[],[f12])).
% 0.20/0.55  fof(f12,plain,(
% 0.20/0.55    ? [X0] : (? [X1] : (? [X2] : (k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f11])).
% 0.20/0.55  fof(f11,negated_conjecture,(
% 0.20/0.55    ~! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) = X1)))),
% 0.20/0.55    inference(negated_conjecture,[],[f10])).
% 0.20/0.55  fof(f10,conjecture,(
% 0.20/0.55    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k12_lattice3(X0,X1,k13_lattice3(X0,X1,X2)) = X1)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_lattice3)).
% 0.20/0.55  fof(f457,plain,(
% 0.20/0.55    ~v3_orders_2(sK0)),
% 0.20/0.55    inference(subsumption_resolution,[],[f456,f49])).
% 0.20/0.55  fof(f49,plain,(
% 0.20/0.55    v2_lattice3(sK0)),
% 0.20/0.55    inference(cnf_transformation,[],[f35])).
% 0.20/0.55  fof(f456,plain,(
% 0.20/0.55    ~v2_lattice3(sK0) | ~v3_orders_2(sK0)),
% 0.20/0.55    inference(subsumption_resolution,[],[f455,f47])).
% 0.20/0.55  fof(f47,plain,(
% 0.20/0.55    v5_orders_2(sK0)),
% 0.20/0.55    inference(cnf_transformation,[],[f35])).
% 0.20/0.55  fof(f455,plain,(
% 0.20/0.55    ~v5_orders_2(sK0) | ~v2_lattice3(sK0) | ~v3_orders_2(sK0)),
% 0.20/0.55    inference(subsumption_resolution,[],[f454,f48])).
% 0.20/0.55  fof(f48,plain,(
% 0.20/0.55    v1_lattice3(sK0)),
% 0.20/0.55    inference(cnf_transformation,[],[f35])).
% 0.20/0.55  fof(f454,plain,(
% 0.20/0.55    ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v2_lattice3(sK0) | ~v3_orders_2(sK0)),
% 0.20/0.55    inference(subsumption_resolution,[],[f453,f50])).
% 0.20/0.55  fof(f50,plain,(
% 0.20/0.55    l1_orders_2(sK0)),
% 0.20/0.55    inference(cnf_transformation,[],[f35])).
% 0.20/0.55  fof(f453,plain,(
% 0.20/0.55    ~l1_orders_2(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v2_lattice3(sK0) | ~v3_orders_2(sK0)),
% 0.20/0.55    inference(subsumption_resolution,[],[f452,f51])).
% 0.20/0.55  fof(f51,plain,(
% 0.20/0.55    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.55    inference(cnf_transformation,[],[f35])).
% 0.20/0.55  fof(f452,plain,(
% 0.20/0.55    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~v2_lattice3(sK0) | ~v3_orders_2(sK0)),
% 0.20/0.55    inference(resolution,[],[f451,f113])).
% 0.20/0.55  fof(f113,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r1_orders_2(X1,X0,X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_orders_2(X1) | ~v1_lattice3(X1) | ~v5_orders_2(X1) | ~v2_lattice3(X1) | ~v3_orders_2(X1)) )),
% 0.20/0.55    inference(condensation,[],[f112])).
% 0.20/0.55  fof(f112,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (r1_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v2_lattice3(X0) | ~v3_orders_2(X0)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f111,f72])).
% 0.20/0.55  fof(f72,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f27])).
% 0.20/0.55  fof(f27,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 0.20/0.55    inference(flattening,[],[f26])).
% 0.20/0.55  fof(f26,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f4])).
% 0.20/0.55  fof(f4,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k12_lattice3)).
% 0.20/0.55  fof(f111,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (r1_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v2_lattice3(X0) | ~v3_orders_2(X0)) )),
% 0.20/0.55    inference(duplicate_literal_removal,[],[f110])).
% 0.20/0.55  fof(f110,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (r1_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0)) )),
% 0.20/0.55    inference(superposition,[],[f86,f107])).
% 0.20/0.55  fof(f107,plain,(
% 0.20/0.55    ( ! [X4,X5,X3] : (k10_lattice3(X3,k12_lattice3(X3,X4,X5),X5) = X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~l1_orders_2(X3) | ~v2_lattice3(X3) | ~v1_lattice3(X3) | ~v5_orders_2(X3) | ~v3_orders_2(X3)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f106,f72])).
% 0.20/0.55  fof(f106,plain,(
% 0.20/0.55    ( ! [X4,X5,X3] : (k10_lattice3(X3,k12_lattice3(X3,X4,X5),X5) = X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~l1_orders_2(X3) | ~v2_lattice3(X3) | ~v1_lattice3(X3) | ~v5_orders_2(X3) | ~v3_orders_2(X3) | ~m1_subset_1(k12_lattice3(X3,X4,X5),u1_struct_0(X3))) )),
% 0.20/0.55    inference(duplicate_literal_removal,[],[f103])).
% 0.20/0.55  fof(f103,plain,(
% 0.20/0.55    ( ! [X4,X5,X3] : (k10_lattice3(X3,k12_lattice3(X3,X4,X5),X5) = X5 | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~l1_orders_2(X3) | ~v2_lattice3(X3) | ~v1_lattice3(X3) | ~v5_orders_2(X3) | ~v3_orders_2(X3) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(k12_lattice3(X3,X4,X5),u1_struct_0(X3)) | ~l1_orders_2(X3) | ~v1_lattice3(X3) | ~v5_orders_2(X3)) )),
% 0.20/0.55    inference(superposition,[],[f70,f71])).
% 0.20/0.55  fof(f71,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f25])).
% 0.20/0.55  fof(f25,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 0.20/0.55    inference(flattening,[],[f24])).
% 0.20/0.55  fof(f24,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f8])).
% 0.20/0.55  fof(f8,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k13_lattice3)).
% 0.20/0.55  fof(f70,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f23])).
% 0.20/0.55  fof(f23,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (! [X2] : (k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0))),
% 0.20/0.55    inference(flattening,[],[f22])).
% 0.20/0.55  fof(f22,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (! [X2] : (k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v3_orders_2(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f9])).
% 0.20/0.55  fof(f9,axiom,(
% 0.20/0.55    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_lattice3)).
% 0.20/0.55  fof(f86,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (r1_orders_2(X0,X2,k10_lattice3(X0,X1,X2)) | ~m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f76,f54])).
% 0.20/0.55  fof(f54,plain,(
% 0.20/0.55    ( ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f15])).
% 0.20/0.55  fof(f15,plain,(
% 0.20/0.55    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 0.20/0.55    inference(flattening,[],[f14])).
% 0.20/0.55  fof(f14,plain,(
% 0.20/0.55    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f1])).
% 0.20/0.55  fof(f1,axiom,(
% 0.20/0.55    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).
% 0.20/0.55  fof(f76,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (r1_orders_2(X0,X2,k10_lattice3(X0,X1,X2)) | ~m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.55    inference(equality_resolution,[],[f57])).
% 0.20/0.55  fof(f57,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X2,X3) | k10_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f40])).
% 0.20/0.55  fof(f40,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,X3,sK3(X0,X1,X2,X3)) & r1_orders_2(X0,X2,sK3(X0,X1,X2,X3)) & r1_orders_2(X0,X1,sK3(X0,X1,X2,X3)) & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f38,f39])).
% 0.20/0.55  fof(f39,plain,(
% 0.20/0.55    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,X3,sK3(X0,X1,X2,X3)) & r1_orders_2(X0,X2,sK3(X0,X1,X2,X3)) & r1_orders_2(X0,X1,sK3(X0,X1,X2,X3)) & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0))))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f38,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.55    inference(rectify,[],[f37])).
% 0.20/0.55  fof(f37,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.55    inference(flattening,[],[f36])).
% 0.20/0.55  fof(f36,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3))) & ((! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.55    inference(nnf_transformation,[],[f19])).
% 0.20/0.55  fof(f19,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.55    inference(flattening,[],[f18])).
% 0.20/0.55  fof(f18,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X3,X4) | (~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f5])).
% 0.20/0.55  fof(f5,axiom,(
% 0.20/0.55    ! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4)) => r1_orders_2(X0,X3,X4))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)))))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l26_lattice3)).
% 0.20/0.55  fof(f451,plain,(
% 0.20/0.55    ~r1_orders_2(sK0,sK1,sK1)),
% 0.20/0.55    inference(subsumption_resolution,[],[f450,f50])).
% 0.20/0.55  fof(f450,plain,(
% 0.20/0.55    ~r1_orders_2(sK0,sK1,sK1) | ~l1_orders_2(sK0)),
% 0.20/0.55    inference(subsumption_resolution,[],[f449,f51])).
% 0.20/0.55  fof(f449,plain,(
% 0.20/0.55    ~r1_orders_2(sK0,sK1,sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0)),
% 0.20/0.55    inference(subsumption_resolution,[],[f444,f52])).
% 0.20/0.55  fof(f52,plain,(
% 0.20/0.55    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.20/0.55    inference(cnf_transformation,[],[f35])).
% 0.20/0.55  fof(f444,plain,(
% 0.20/0.55    ~r1_orders_2(sK0,sK1,sK1) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0)),
% 0.20/0.55    inference(resolution,[],[f443,f74])).
% 0.20/0.55  fof(f74,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f31])).
% 0.20/0.55  fof(f31,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 0.20/0.55    inference(flattening,[],[f30])).
% 0.20/0.55  fof(f30,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f3])).
% 0.20/0.55  fof(f3,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0)) => m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_lattice3)).
% 0.20/0.55  fof(f443,plain,(
% 0.20/0.55    ~m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK1,sK1)),
% 0.20/0.55    inference(subsumption_resolution,[],[f442,f47])).
% 0.20/0.55  fof(f442,plain,(
% 0.20/0.55    ~r1_orders_2(sK0,sK1,sK1) | ~m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | ~v5_orders_2(sK0)),
% 0.20/0.55    inference(subsumption_resolution,[],[f441,f48])).
% 0.20/0.55  fof(f441,plain,(
% 0.20/0.55    ~r1_orders_2(sK0,sK1,sK1) | ~m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0)),
% 0.20/0.55    inference(subsumption_resolution,[],[f440,f50])).
% 0.20/0.55  fof(f440,plain,(
% 0.20/0.55    ~r1_orders_2(sK0,sK1,sK1) | ~m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0)),
% 0.20/0.55    inference(subsumption_resolution,[],[f439,f51])).
% 0.20/0.55  fof(f439,plain,(
% 0.20/0.55    ~r1_orders_2(sK0,sK1,sK1) | ~m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0)),
% 0.20/0.55    inference(subsumption_resolution,[],[f438,f52])).
% 0.20/0.55  fof(f438,plain,(
% 0.20/0.55    ~r1_orders_2(sK0,sK1,sK1) | ~m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0)),
% 0.20/0.55    inference(duplicate_literal_removal,[],[f433])).
% 0.20/0.55  fof(f433,plain,(
% 0.20/0.55    ~r1_orders_2(sK0,sK1,sK1) | ~m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | ~m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0)),
% 0.20/0.55    inference(resolution,[],[f414,f87])).
% 0.20/0.55  fof(f87,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2)) | ~m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f77,f54])).
% 0.20/0.55  fof(f77,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2)) | ~m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.55    inference(equality_resolution,[],[f56])).
% 0.20/0.55  fof(f56,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X1,X3) | k10_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f40])).
% 0.20/0.55  fof(f414,plain,(
% 0.20/0.55    ~r1_orders_2(sK0,sK1,k10_lattice3(sK0,sK1,sK2)) | ~r1_orders_2(sK0,sK1,sK1) | ~m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))),
% 0.20/0.55    inference(subsumption_resolution,[],[f413,f47])).
% 0.20/0.55  fof(f413,plain,(
% 0.20/0.55    ~r1_orders_2(sK0,sK1,k10_lattice3(sK0,sK1,sK2)) | ~r1_orders_2(sK0,sK1,sK1) | ~m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | ~v5_orders_2(sK0)),
% 0.20/0.55    inference(subsumption_resolution,[],[f412,f49])).
% 0.20/0.55  fof(f412,plain,(
% 0.20/0.55    ~r1_orders_2(sK0,sK1,k10_lattice3(sK0,sK1,sK2)) | ~r1_orders_2(sK0,sK1,sK1) | ~m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | ~v2_lattice3(sK0) | ~v5_orders_2(sK0)),
% 0.20/0.55    inference(subsumption_resolution,[],[f411,f50])).
% 0.20/0.55  fof(f411,plain,(
% 0.20/0.55    ~r1_orders_2(sK0,sK1,k10_lattice3(sK0,sK1,sK2)) | ~r1_orders_2(sK0,sK1,sK1) | ~m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0) | ~v5_orders_2(sK0)),
% 0.20/0.55    inference(subsumption_resolution,[],[f409,f51])).
% 0.20/0.55  fof(f409,plain,(
% 0.20/0.55    ~r1_orders_2(sK0,sK1,k10_lattice3(sK0,sK1,sK2)) | ~r1_orders_2(sK0,sK1,sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0) | ~v5_orders_2(sK0)),
% 0.20/0.55    inference(trivial_inequality_removal,[],[f383])).
% 0.20/0.55  fof(f383,plain,(
% 0.20/0.55    sK1 != sK1 | ~r1_orders_2(sK0,sK1,k10_lattice3(sK0,sK1,sK2)) | ~r1_orders_2(sK0,sK1,sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k10_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0) | ~v5_orders_2(sK0)),
% 0.20/0.55    inference(superposition,[],[f102,f380])).
% 0.20/0.55  fof(f380,plain,(
% 0.20/0.55    ( ! [X6,X8,X7] : (k12_lattice3(X6,X7,X8) = X7 | ~r1_orders_2(X6,X7,X8) | ~r1_orders_2(X6,X7,X7) | ~m1_subset_1(X7,u1_struct_0(X6)) | ~m1_subset_1(X8,u1_struct_0(X6)) | ~l1_orders_2(X6) | ~v2_lattice3(X6) | ~v5_orders_2(X6)) )),
% 0.20/0.55    inference(duplicate_literal_removal,[],[f368])).
% 0.20/0.55  fof(f368,plain,(
% 0.20/0.55    ( ! [X6,X8,X7] : (k12_lattice3(X6,X7,X8) = X7 | ~r1_orders_2(X6,X7,X8) | ~r1_orders_2(X6,X7,X7) | ~m1_subset_1(X7,u1_struct_0(X6)) | ~m1_subset_1(X8,u1_struct_0(X6)) | ~l1_orders_2(X6) | ~v2_lattice3(X6) | ~v5_orders_2(X6) | ~m1_subset_1(X8,u1_struct_0(X6)) | ~m1_subset_1(X7,u1_struct_0(X6)) | ~l1_orders_2(X6) | ~v2_lattice3(X6) | ~v5_orders_2(X6)) )),
% 0.20/0.55    inference(superposition,[],[f335,f73])).
% 0.20/0.55  fof(f73,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f29])).
% 0.20/0.55  fof(f29,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 0.20/0.55    inference(flattening,[],[f28])).
% 0.20/0.55  fof(f28,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f7])).
% 0.20/0.55  fof(f7,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k12_lattice3)).
% 0.20/0.55  fof(f335,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (k11_lattice3(X0,X1,X2) = X1 | ~r1_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.20/0.55    inference(duplicate_literal_removal,[],[f332])).
% 0.20/0.55  fof(f332,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (k11_lattice3(X0,X1,X2) = X1 | ~r1_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | k11_lattice3(X0,X1,X2) = X1 | ~r1_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.20/0.55    inference(resolution,[],[f90,f88])).
% 0.20/0.55  fof(f88,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (~r1_orders_2(X0,sK4(X0,X1,X2,X3),X3) | k11_lattice3(X0,X1,X2) = X3 | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f69,f55])).
% 0.20/0.55  fof(f55,plain,(
% 0.20/0.55    ( ! [X0] : (~v2_lattice3(X0) | ~v2_struct_0(X0) | ~l1_orders_2(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f17])).
% 0.20/0.55  fof(f17,plain,(
% 0.20/0.55    ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0))),
% 0.20/0.55    inference(flattening,[],[f16])).
% 0.20/0.55  fof(f16,plain,(
% 0.20/0.55    ! [X0] : ((~v2_struct_0(X0) | ~v2_lattice3(X0)) | ~l1_orders_2(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f2])).
% 0.20/0.55  fof(f2,axiom,(
% 0.20/0.55    ! [X0] : (l1_orders_2(X0) => (v2_lattice3(X0) => ~v2_struct_0(X0)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).
% 0.20/0.55  fof(f69,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (k11_lattice3(X0,X1,X2) = X3 | ~r1_orders_2(X0,sK4(X0,X1,X2,X3),X3) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f45])).
% 0.20/0.55  fof(f45,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,sK4(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK4(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK4(X0,X1,X2,X3),X1) & m1_subset_1(sK4(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f43,f44])).
% 0.20/0.55  fof(f44,plain,(
% 0.20/0.55    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,sK4(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK4(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK4(X0,X1,X2,X3),X1) & m1_subset_1(sK4(X0,X1,X2,X3),u1_struct_0(X0))))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f43,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.55    inference(rectify,[],[f42])).
% 0.20/0.55  fof(f42,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.55    inference(flattening,[],[f41])).
% 0.20/0.55  fof(f41,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1))) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.55    inference(nnf_transformation,[],[f21])).
% 0.20/0.55  fof(f21,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.55    inference(flattening,[],[f20])).
% 0.20/0.55  fof(f20,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X4,X3) | (~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f6])).
% 0.20/0.55  fof(f6,axiom,(
% 0.20/0.55    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1)) => r1_orders_2(X0,X4,X3))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)))))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l28_lattice3)).
% 0.20/0.55  fof(f90,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,sK4(X0,X1,X2,X3),X1) | k11_lattice3(X0,X1,X2) = X3 | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f67,f55])).
% 0.20/0.55  fof(f67,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (k11_lattice3(X0,X1,X2) = X3 | r1_orders_2(X0,sK4(X0,X1,X2,X3),X1) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f45])).
% 0.20/0.55  fof(f102,plain,(
% 0.20/0.55    sK1 != k12_lattice3(sK0,sK1,k10_lattice3(sK0,sK1,sK2))),
% 0.20/0.55    inference(subsumption_resolution,[],[f101,f47])).
% 0.20/0.55  fof(f101,plain,(
% 0.20/0.55    sK1 != k12_lattice3(sK0,sK1,k10_lattice3(sK0,sK1,sK2)) | ~v5_orders_2(sK0)),
% 0.20/0.55    inference(subsumption_resolution,[],[f100,f48])).
% 0.20/0.55  fof(f100,plain,(
% 0.20/0.55    sK1 != k12_lattice3(sK0,sK1,k10_lattice3(sK0,sK1,sK2)) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0)),
% 0.20/0.55    inference(subsumption_resolution,[],[f99,f50])).
% 0.20/0.55  fof(f99,plain,(
% 0.20/0.55    sK1 != k12_lattice3(sK0,sK1,k10_lattice3(sK0,sK1,sK2)) | ~l1_orders_2(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0)),
% 0.20/0.55    inference(subsumption_resolution,[],[f98,f51])).
% 0.20/0.56  fof(f98,plain,(
% 0.20/0.56    sK1 != k12_lattice3(sK0,sK1,k10_lattice3(sK0,sK1,sK2)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0)),
% 0.20/0.56    inference(subsumption_resolution,[],[f97,f52])).
% 0.20/0.56  fof(f97,plain,(
% 0.20/0.56    sK1 != k12_lattice3(sK0,sK1,k10_lattice3(sK0,sK1,sK2)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0)),
% 0.20/0.56    inference(superposition,[],[f53,f71])).
% 0.20/0.56  fof(f53,plain,(
% 0.20/0.56    sK1 != k12_lattice3(sK0,sK1,k13_lattice3(sK0,sK1,sK2))),
% 0.20/0.56    inference(cnf_transformation,[],[f35])).
% 0.20/0.56  % SZS output end Proof for theBenchmark
% 0.20/0.56  % (8083)------------------------------
% 0.20/0.56  % (8083)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (8083)Termination reason: Refutation
% 0.20/0.56  
% 0.20/0.56  % (8083)Memory used [KB]: 1791
% 0.20/0.56  % (8083)Time elapsed: 0.105 s
% 0.20/0.56  % (8083)------------------------------
% 0.20/0.56  % (8083)------------------------------
% 0.20/0.56  % (8059)Success in time 0.198 s
%------------------------------------------------------------------------------
