%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:34 EST 2020

% Result     : Theorem 1.35s
% Output     : Refutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 419 expanded)
%              Number of leaves         :   17 ( 152 expanded)
%              Depth                    :   19
%              Number of atoms          :  739 (3017 expanded)
%              Number of equality atoms :   58 ( 416 expanded)
%              Maximal formula depth    :   22 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f394,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f115,f136,f178,f393])).

fof(f393,plain,(
    spl5_3 ),
    inference(avatar_contradiction_clause,[],[f392])).

fof(f392,plain,
    ( $false
    | spl5_3 ),
    inference(subsumption_resolution,[],[f391,f44])).

fof(f44,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( sK2 != k13_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2)
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v2_lattice3(sK0)
    & v1_lattice3(sK0)
    & v5_orders_2(sK0)
    & v3_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f31,f30,f29])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) != X2
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k13_lattice3(sK0,k12_lattice3(sK0,X1,X2),X2) != X2
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v2_lattice3(sK0)
      & v1_lattice3(sK0)
      & v5_orders_2(sK0)
      & v3_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k13_lattice3(sK0,k12_lattice3(sK0,X1,X2),X2) != X2
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( k13_lattice3(sK0,k12_lattice3(sK0,sK1,X2),X2) != X2
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X2] :
        ( k13_lattice3(sK0,k12_lattice3(sK0,sK1,X2),X2) != X2
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( sK2 != k13_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2)
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) != X2
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) != X2
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
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
               => k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2 ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
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

fof(f391,plain,
    ( ~ v5_orders_2(sK0)
    | spl5_3 ),
    inference(subsumption_resolution,[],[f390,f46])).

fof(f46,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f390,plain,
    ( ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | spl5_3 ),
    inference(subsumption_resolution,[],[f389,f47])).

fof(f47,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f389,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | spl5_3 ),
    inference(subsumption_resolution,[],[f388,f48])).

fof(f48,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f32])).

fof(f388,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | spl5_3 ),
    inference(subsumption_resolution,[],[f383,f49])).

fof(f49,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f32])).

fof(f383,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | spl5_3 ),
    inference(resolution,[],[f196,f129])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f128])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f89,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k11_lattice3)).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f75,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v2_lattice3(X0)
      | ~ v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,X2)
      | k11_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f41])).

fof(f41,plain,(
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

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

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

fof(f196,plain,
    ( ~ r1_orders_2(sK0,k11_lattice3(sK0,sK1,sK2),sK2)
    | spl5_3 ),
    inference(subsumption_resolution,[],[f195,f44])).

fof(f195,plain,
    ( ~ r1_orders_2(sK0,k11_lattice3(sK0,sK1,sK2),sK2)
    | ~ v5_orders_2(sK0)
    | spl5_3 ),
    inference(subsumption_resolution,[],[f194,f46])).

fof(f194,plain,
    ( ~ r1_orders_2(sK0,k11_lattice3(sK0,sK1,sK2),sK2)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | spl5_3 ),
    inference(subsumption_resolution,[],[f193,f47])).

fof(f193,plain,
    ( ~ r1_orders_2(sK0,k11_lattice3(sK0,sK1,sK2),sK2)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | spl5_3 ),
    inference(subsumption_resolution,[],[f192,f48])).

fof(f192,plain,
    ( ~ r1_orders_2(sK0,k11_lattice3(sK0,sK1,sK2),sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | spl5_3 ),
    inference(subsumption_resolution,[],[f191,f49])).

fof(f191,plain,
    ( ~ r1_orders_2(sK0,k11_lattice3(sK0,sK1,sK2),sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | spl5_3 ),
    inference(superposition,[],[f177,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

% (11261)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

fof(f177,plain,
    ( ~ r1_orders_2(sK0,k12_lattice3(sK0,sK1,sK2),sK2)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f176])).

fof(f176,plain,
    ( spl5_3
  <=> r1_orders_2(sK0,k12_lattice3(sK0,sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f178,plain,
    ( ~ spl5_1
    | ~ spl5_3
    | spl5_2 ),
    inference(avatar_split_clause,[],[f174,f113,f176,f110])).

fof(f110,plain,
    ( spl5_1
  <=> m1_subset_1(k12_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f113,plain,
    ( spl5_2
  <=> sK2 = k10_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f174,plain,
    ( ~ r1_orders_2(sK0,k12_lattice3(sK0,sK1,sK2),sK2)
    | ~ m1_subset_1(k12_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | spl5_2 ),
    inference(subsumption_resolution,[],[f173,f44])).

fof(f173,plain,
    ( ~ r1_orders_2(sK0,k12_lattice3(sK0,sK1,sK2),sK2)
    | ~ m1_subset_1(k12_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | spl5_2 ),
    inference(subsumption_resolution,[],[f172,f45])).

fof(f45,plain,(
    v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f172,plain,
    ( ~ r1_orders_2(sK0,k12_lattice3(sK0,sK1,sK2),sK2)
    | ~ m1_subset_1(k12_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | spl5_2 ),
    inference(subsumption_resolution,[],[f171,f47])).

fof(f171,plain,
    ( ~ r1_orders_2(sK0,k12_lattice3(sK0,sK1,sK2),sK2)
    | ~ m1_subset_1(k12_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | spl5_2 ),
    inference(subsumption_resolution,[],[f170,f49])).

fof(f170,plain,
    ( ~ r1_orders_2(sK0,k12_lattice3(sK0,sK1,sK2),sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(k12_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | spl5_2 ),
    inference(subsumption_resolution,[],[f166,f101])).

fof(f101,plain,(
    r1_orders_2(sK0,sK2,sK2) ),
    inference(subsumption_resolution,[],[f100,f92])).

fof(f92,plain,(
    ~ v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f91,f47])).

fof(f91,plain,
    ( ~ v2_struct_0(sK0)
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f51,f45])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_lattice3(X0)
      | ~ v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).

fof(f100,plain,
    ( r1_orders_2(sK0,sK2,sK2)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f99,f43])).

fof(f43,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f99,plain,
    ( r1_orders_2(sK0,sK2,sK2)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f95,f47])).

fof(f95,plain,
    ( r1_orders_2(sK0,sK2,sK2)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f53,f49])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X1)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,X1,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_orders_2)).

fof(f166,plain,
    ( ~ r1_orders_2(sK0,sK2,sK2)
    | ~ r1_orders_2(sK0,k12_lattice3(sK0,sK1,sK2),sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(k12_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | spl5_2 ),
    inference(trivial_inequality_removal,[],[f163])).

fof(f163,plain,
    ( sK2 != sK2
    | ~ r1_orders_2(sK0,sK2,sK2)
    | ~ r1_orders_2(sK0,k12_lattice3(sK0,sK1,sK2),sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(k12_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | spl5_2 ),
    inference(superposition,[],[f114,f138])).

fof(f138,plain,(
    ! [X2,X0,X1] :
      ( k10_lattice3(X0,X1,X2) = X2
      | ~ r1_orders_2(X0,X2,X2)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f137])).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( k10_lattice3(X0,X1,X2) = X2
      | ~ r1_orders_2(X0,X2,X2)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | k10_lattice3(X0,X1,X2) = X2
      | ~ r1_orders_2(X0,X2,X2)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(resolution,[],[f78,f77])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,X3,sK3(X0,X1,X2,X3))
      | k10_lattice3(X0,X1,X2) = X3
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f60,f51])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_lattice3(X0,X1,X2) = X3
      | ~ r1_orders_2(X0,X3,sK3(X0,X1,X2,X3))
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f36])).

fof(f36,plain,(
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

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

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

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X2,sK3(X0,X1,X2,X3))
      | k10_lattice3(X0,X1,X2) = X3
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f59,f51])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_lattice3(X0,X1,X2) = X3
      | r1_orders_2(X0,X2,sK3(X0,X1,X2,X3))
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f114,plain,
    ( sK2 != k10_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f113])).

fof(f136,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f135])).

fof(f135,plain,
    ( $false
    | spl5_1 ),
    inference(subsumption_resolution,[],[f134,f47])).

fof(f134,plain,
    ( ~ l1_orders_2(sK0)
    | spl5_1 ),
    inference(subsumption_resolution,[],[f133,f48])).

fof(f133,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | spl5_1 ),
    inference(subsumption_resolution,[],[f132,f49])).

fof(f132,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | spl5_1 ),
    inference(resolution,[],[f127,f70])).

fof(f127,plain,
    ( ~ m1_subset_1(k11_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | spl5_1 ),
    inference(subsumption_resolution,[],[f126,f44])).

fof(f126,plain,
    ( ~ m1_subset_1(k11_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | spl5_1 ),
    inference(subsumption_resolution,[],[f125,f46])).

fof(f125,plain,
    ( ~ m1_subset_1(k11_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | spl5_1 ),
    inference(subsumption_resolution,[],[f124,f47])).

fof(f124,plain,
    ( ~ m1_subset_1(k11_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | spl5_1 ),
    inference(subsumption_resolution,[],[f123,f48])).

fof(f123,plain,
    ( ~ m1_subset_1(k11_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | spl5_1 ),
    inference(subsumption_resolution,[],[f122,f49])).

fof(f122,plain,
    ( ~ m1_subset_1(k11_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | spl5_1 ),
    inference(superposition,[],[f111,f69])).

fof(f111,plain,
    ( ~ m1_subset_1(k12_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f110])).

fof(f115,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f108,f113,f110])).

fof(f108,plain,
    ( sK2 != k10_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2)
    | ~ m1_subset_1(k12_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f107,f44])).

fof(f107,plain,
    ( sK2 != k10_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2)
    | ~ m1_subset_1(k12_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f106,f45])).

fof(f106,plain,
    ( sK2 != k10_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2)
    | ~ m1_subset_1(k12_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f105,f47])).

fof(f105,plain,
    ( sK2 != k10_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2)
    | ~ m1_subset_1(k12_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f104,f49])).

fof(f104,plain,
    ( sK2 != k10_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(k12_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(superposition,[],[f50,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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

fof(f50,plain,(
    sK2 != k13_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:50:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.43  % (11275)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.50  % (11265)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.52  % (11274)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.52  % (11271)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.52  % (11269)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.52  % (11266)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.52  % (11279)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 1.35/0.53  % (11270)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 1.35/0.53  % (11267)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 1.35/0.53  % (11278)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 1.35/0.53  % (11262)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 1.35/0.53  % (11268)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 1.35/0.53  % (11273)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 1.35/0.53  % (11263)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 1.35/0.54  % (11264)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 1.35/0.54  % (11262)Refutation found. Thanks to Tanya!
% 1.35/0.54  % SZS status Theorem for theBenchmark
% 1.35/0.54  % SZS output start Proof for theBenchmark
% 1.35/0.54  fof(f394,plain,(
% 1.35/0.54    $false),
% 1.35/0.54    inference(avatar_sat_refutation,[],[f115,f136,f178,f393])).
% 1.35/0.54  fof(f393,plain,(
% 1.35/0.54    spl5_3),
% 1.35/0.54    inference(avatar_contradiction_clause,[],[f392])).
% 1.35/0.54  fof(f392,plain,(
% 1.35/0.54    $false | spl5_3),
% 1.35/0.54    inference(subsumption_resolution,[],[f391,f44])).
% 1.35/0.54  fof(f44,plain,(
% 1.35/0.54    v5_orders_2(sK0)),
% 1.35/0.54    inference(cnf_transformation,[],[f32])).
% 1.35/0.54  fof(f32,plain,(
% 1.35/0.54    ((sK2 != k13_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v2_lattice3(sK0) & v1_lattice3(sK0) & v5_orders_2(sK0) & v3_orders_2(sK0)),
% 1.35/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f31,f30,f29])).
% 1.35/0.54  fof(f29,plain,(
% 1.35/0.54    ? [X0] : (? [X1] : (? [X2] : (k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => (? [X1] : (? [X2] : (k13_lattice3(sK0,k12_lattice3(sK0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v2_lattice3(sK0) & v1_lattice3(sK0) & v5_orders_2(sK0) & v3_orders_2(sK0))),
% 1.35/0.54    introduced(choice_axiom,[])).
% 1.35/0.54  fof(f30,plain,(
% 1.35/0.54    ? [X1] : (? [X2] : (k13_lattice3(sK0,k12_lattice3(sK0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (k13_lattice3(sK0,k12_lattice3(sK0,sK1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 1.35/0.54    introduced(choice_axiom,[])).
% 1.35/0.54  fof(f31,plain,(
% 1.35/0.54    ? [X2] : (k13_lattice3(sK0,k12_lattice3(sK0,sK1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(sK0))) => (sK2 != k13_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 1.35/0.54    introduced(choice_axiom,[])).
% 1.35/0.54  fof(f12,plain,(
% 1.35/0.54    ? [X0] : (? [X1] : (? [X2] : (k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0))),
% 1.35/0.54    inference(flattening,[],[f11])).
% 1.35/0.54  fof(f11,plain,(
% 1.35/0.54    ? [X0] : (? [X1] : (? [X2] : (k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)))),
% 1.35/0.54    inference(ennf_transformation,[],[f10])).
% 1.35/0.54  fof(f10,negated_conjecture,(
% 1.35/0.54    ~! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2)))),
% 1.35/0.54    inference(negated_conjecture,[],[f9])).
% 1.35/0.54  fof(f9,conjecture,(
% 1.35/0.54    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k13_lattice3(X0,k12_lattice3(X0,X1,X2),X2) = X2)))),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_lattice3)).
% 1.35/0.54  fof(f391,plain,(
% 1.35/0.54    ~v5_orders_2(sK0) | spl5_3),
% 1.35/0.54    inference(subsumption_resolution,[],[f390,f46])).
% 1.35/0.54  fof(f46,plain,(
% 1.35/0.54    v2_lattice3(sK0)),
% 1.35/0.54    inference(cnf_transformation,[],[f32])).
% 1.35/0.54  fof(f390,plain,(
% 1.35/0.54    ~v2_lattice3(sK0) | ~v5_orders_2(sK0) | spl5_3),
% 1.35/0.54    inference(subsumption_resolution,[],[f389,f47])).
% 1.35/0.54  fof(f47,plain,(
% 1.35/0.54    l1_orders_2(sK0)),
% 1.35/0.54    inference(cnf_transformation,[],[f32])).
% 1.35/0.54  fof(f389,plain,(
% 1.35/0.54    ~l1_orders_2(sK0) | ~v2_lattice3(sK0) | ~v5_orders_2(sK0) | spl5_3),
% 1.35/0.54    inference(subsumption_resolution,[],[f388,f48])).
% 1.35/0.54  fof(f48,plain,(
% 1.35/0.54    m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.35/0.54    inference(cnf_transformation,[],[f32])).
% 1.35/0.54  fof(f388,plain,(
% 1.35/0.54    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0) | ~v5_orders_2(sK0) | spl5_3),
% 1.35/0.54    inference(subsumption_resolution,[],[f383,f49])).
% 1.35/0.54  fof(f49,plain,(
% 1.35/0.54    m1_subset_1(sK2,u1_struct_0(sK0))),
% 1.35/0.54    inference(cnf_transformation,[],[f32])).
% 1.35/0.54  fof(f383,plain,(
% 1.35/0.54    ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0) | ~v5_orders_2(sK0) | spl5_3),
% 1.35/0.54    inference(resolution,[],[f196,f129])).
% 1.35/0.54  fof(f129,plain,(
% 1.35/0.54    ( ! [X2,X0,X1] : (r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 1.35/0.54    inference(duplicate_literal_removal,[],[f128])).
% 1.35/0.54  fof(f128,plain,(
% 1.35/0.54    ( ! [X2,X0,X1] : (r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.35/0.54    inference(resolution,[],[f89,f70])).
% 1.35/0.54  fof(f70,plain,(
% 1.35/0.54    ( ! [X2,X0,X1] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f28])).
% 1.35/0.54  fof(f28,plain,(
% 1.35/0.54    ! [X0,X1,X2] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 1.35/0.54    inference(flattening,[],[f27])).
% 1.35/0.54  fof(f27,plain,(
% 1.35/0.54    ! [X0,X1,X2] : (m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)))),
% 1.35/0.54    inference(ennf_transformation,[],[f4])).
% 1.35/0.54  fof(f4,axiom,(
% 1.35/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0)) => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)))),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k11_lattice3)).
% 1.35/0.54  fof(f89,plain,(
% 1.35/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 1.35/0.54    inference(subsumption_resolution,[],[f75,f52])).
% 1.35/0.54  fof(f52,plain,(
% 1.35/0.54    ( ! [X0] : (~v2_lattice3(X0) | ~v2_struct_0(X0) | ~l1_orders_2(X0)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f16])).
% 1.35/0.54  fof(f16,plain,(
% 1.35/0.54    ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0))),
% 1.35/0.54    inference(flattening,[],[f15])).
% 1.35/0.54  fof(f15,plain,(
% 1.35/0.54    ! [X0] : ((~v2_struct_0(X0) | ~v2_lattice3(X0)) | ~l1_orders_2(X0))),
% 1.35/0.54    inference(ennf_transformation,[],[f3])).
% 1.35/0.54  fof(f3,axiom,(
% 1.35/0.54    ! [X0] : (l1_orders_2(X0) => (v2_lattice3(X0) => ~v2_struct_0(X0)))),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).
% 1.35/0.54  fof(f75,plain,(
% 1.35/0.54    ( ! [X2,X0,X1] : (r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2) | ~m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 1.35/0.54    inference(equality_resolution,[],[f62])).
% 1.35/0.54  fof(f62,plain,(
% 1.35/0.54    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X3,X2) | k11_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f42])).
% 1.35/0.54  fof(f42,plain,(
% 1.35/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,sK4(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK4(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK4(X0,X1,X2,X3),X1) & m1_subset_1(sK4(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.35/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f41])).
% 1.35/0.54  fof(f41,plain,(
% 1.35/0.54    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,sK4(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK4(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK4(X0,X1,X2,X3),X1) & m1_subset_1(sK4(X0,X1,X2,X3),u1_struct_0(X0))))),
% 1.35/0.54    introduced(choice_axiom,[])).
% 1.35/0.54  fof(f40,plain,(
% 1.35/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.35/0.54    inference(rectify,[],[f39])).
% 1.35/0.54  fof(f39,plain,(
% 1.35/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.35/0.54    inference(flattening,[],[f38])).
% 1.35/0.54  fof(f38,plain,(
% 1.35/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1))) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.35/0.54    inference(nnf_transformation,[],[f22])).
% 1.48/0.54  fof(f22,plain,(
% 1.48/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.48/0.54    inference(flattening,[],[f21])).
% 1.48/0.54  fof(f21,plain,(
% 1.48/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X4,X3) | (~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 1.48/0.54    inference(ennf_transformation,[],[f6])).
% 1.48/0.54  fof(f6,axiom,(
% 1.48/0.54    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1)) => r1_orders_2(X0,X4,X3))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)))))))),
% 1.48/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l28_lattice3)).
% 1.48/0.54  fof(f196,plain,(
% 1.48/0.54    ~r1_orders_2(sK0,k11_lattice3(sK0,sK1,sK2),sK2) | spl5_3),
% 1.48/0.54    inference(subsumption_resolution,[],[f195,f44])).
% 1.48/0.54  fof(f195,plain,(
% 1.48/0.54    ~r1_orders_2(sK0,k11_lattice3(sK0,sK1,sK2),sK2) | ~v5_orders_2(sK0) | spl5_3),
% 1.48/0.54    inference(subsumption_resolution,[],[f194,f46])).
% 1.48/0.54  fof(f194,plain,(
% 1.48/0.54    ~r1_orders_2(sK0,k11_lattice3(sK0,sK1,sK2),sK2) | ~v2_lattice3(sK0) | ~v5_orders_2(sK0) | spl5_3),
% 1.48/0.54    inference(subsumption_resolution,[],[f193,f47])).
% 1.48/0.54  fof(f193,plain,(
% 1.48/0.54    ~r1_orders_2(sK0,k11_lattice3(sK0,sK1,sK2),sK2) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0) | ~v5_orders_2(sK0) | spl5_3),
% 1.48/0.54    inference(subsumption_resolution,[],[f192,f48])).
% 1.48/0.54  fof(f192,plain,(
% 1.48/0.54    ~r1_orders_2(sK0,k11_lattice3(sK0,sK1,sK2),sK2) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0) | ~v5_orders_2(sK0) | spl5_3),
% 1.48/0.54    inference(subsumption_resolution,[],[f191,f49])).
% 1.48/0.54  fof(f191,plain,(
% 1.48/0.54    ~r1_orders_2(sK0,k11_lattice3(sK0,sK1,sK2),sK2) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0) | ~v5_orders_2(sK0) | spl5_3),
% 1.48/0.54    inference(superposition,[],[f177,f69])).
% 1.48/0.54  fof(f69,plain,(
% 1.48/0.54    ( ! [X2,X0,X1] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 1.48/0.54    inference(cnf_transformation,[],[f26])).
% 1.48/0.54  fof(f26,plain,(
% 1.48/0.54    ! [X0,X1,X2] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 1.48/0.54    inference(flattening,[],[f25])).
% 1.48/0.54  fof(f25,plain,(
% 1.48/0.54    ! [X0,X1,X2] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 1.48/0.54    inference(ennf_transformation,[],[f7])).
% 1.48/0.54  % (11261)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.48/0.54  fof(f7,axiom,(
% 1.48/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2))),
% 1.48/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k12_lattice3)).
% 1.48/0.54  fof(f177,plain,(
% 1.48/0.54    ~r1_orders_2(sK0,k12_lattice3(sK0,sK1,sK2),sK2) | spl5_3),
% 1.48/0.54    inference(avatar_component_clause,[],[f176])).
% 1.48/0.54  fof(f176,plain,(
% 1.48/0.54    spl5_3 <=> r1_orders_2(sK0,k12_lattice3(sK0,sK1,sK2),sK2)),
% 1.48/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.48/0.54  fof(f178,plain,(
% 1.48/0.54    ~spl5_1 | ~spl5_3 | spl5_2),
% 1.48/0.54    inference(avatar_split_clause,[],[f174,f113,f176,f110])).
% 1.48/0.54  fof(f110,plain,(
% 1.48/0.54    spl5_1 <=> m1_subset_1(k12_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))),
% 1.48/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.48/0.54  fof(f113,plain,(
% 1.48/0.54    spl5_2 <=> sK2 = k10_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2)),
% 1.48/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.48/0.54  fof(f174,plain,(
% 1.48/0.54    ~r1_orders_2(sK0,k12_lattice3(sK0,sK1,sK2),sK2) | ~m1_subset_1(k12_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | spl5_2),
% 1.48/0.54    inference(subsumption_resolution,[],[f173,f44])).
% 1.48/0.54  fof(f173,plain,(
% 1.48/0.54    ~r1_orders_2(sK0,k12_lattice3(sK0,sK1,sK2),sK2) | ~m1_subset_1(k12_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | ~v5_orders_2(sK0) | spl5_2),
% 1.48/0.54    inference(subsumption_resolution,[],[f172,f45])).
% 1.48/0.54  fof(f45,plain,(
% 1.48/0.54    v1_lattice3(sK0)),
% 1.48/0.54    inference(cnf_transformation,[],[f32])).
% 1.48/0.54  fof(f172,plain,(
% 1.48/0.54    ~r1_orders_2(sK0,k12_lattice3(sK0,sK1,sK2),sK2) | ~m1_subset_1(k12_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | spl5_2),
% 1.48/0.54    inference(subsumption_resolution,[],[f171,f47])).
% 1.48/0.54  fof(f171,plain,(
% 1.48/0.54    ~r1_orders_2(sK0,k12_lattice3(sK0,sK1,sK2),sK2) | ~m1_subset_1(k12_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | spl5_2),
% 1.48/0.54    inference(subsumption_resolution,[],[f170,f49])).
% 1.48/0.54  fof(f170,plain,(
% 1.48/0.54    ~r1_orders_2(sK0,k12_lattice3(sK0,sK1,sK2),sK2) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(k12_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | spl5_2),
% 1.48/0.54    inference(subsumption_resolution,[],[f166,f101])).
% 1.48/0.54  fof(f101,plain,(
% 1.48/0.54    r1_orders_2(sK0,sK2,sK2)),
% 1.48/0.54    inference(subsumption_resolution,[],[f100,f92])).
% 1.48/0.54  fof(f92,plain,(
% 1.48/0.54    ~v2_struct_0(sK0)),
% 1.48/0.54    inference(subsumption_resolution,[],[f91,f47])).
% 1.48/0.54  fof(f91,plain,(
% 1.48/0.54    ~v2_struct_0(sK0) | ~l1_orders_2(sK0)),
% 1.48/0.54    inference(resolution,[],[f51,f45])).
% 1.48/0.54  fof(f51,plain,(
% 1.48/0.54    ( ! [X0] : (~v1_lattice3(X0) | ~v2_struct_0(X0) | ~l1_orders_2(X0)) )),
% 1.48/0.54    inference(cnf_transformation,[],[f14])).
% 1.48/0.54  fof(f14,plain,(
% 1.48/0.54    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 1.48/0.54    inference(flattening,[],[f13])).
% 1.48/0.54  fof(f13,plain,(
% 1.48/0.54    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 1.48/0.54    inference(ennf_transformation,[],[f2])).
% 1.48/0.54  fof(f2,axiom,(
% 1.48/0.54    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 1.48/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).
% 1.48/0.54  fof(f100,plain,(
% 1.48/0.54    r1_orders_2(sK0,sK2,sK2) | v2_struct_0(sK0)),
% 1.48/0.54    inference(subsumption_resolution,[],[f99,f43])).
% 1.48/0.54  fof(f43,plain,(
% 1.48/0.54    v3_orders_2(sK0)),
% 1.48/0.54    inference(cnf_transformation,[],[f32])).
% 1.48/0.54  fof(f99,plain,(
% 1.48/0.54    r1_orders_2(sK0,sK2,sK2) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 1.48/0.54    inference(subsumption_resolution,[],[f95,f47])).
% 1.48/0.54  fof(f95,plain,(
% 1.48/0.54    r1_orders_2(sK0,sK2,sK2) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 1.48/0.54    inference(resolution,[],[f53,f49])).
% 1.48/0.54  fof(f53,plain,(
% 1.48/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | r1_orders_2(X0,X1,X1) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.48/0.54    inference(cnf_transformation,[],[f18])).
% 1.48/0.54  fof(f18,plain,(
% 1.48/0.54    ! [X0] : (! [X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.48/0.54    inference(flattening,[],[f17])).
% 1.48/0.54  fof(f17,plain,(
% 1.48/0.54    ! [X0] : (! [X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.48/0.54    inference(ennf_transformation,[],[f1])).
% 1.48/0.54  fof(f1,axiom,(
% 1.48/0.54    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,X1,X1)))),
% 1.48/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_orders_2)).
% 1.48/0.54  fof(f166,plain,(
% 1.48/0.54    ~r1_orders_2(sK0,sK2,sK2) | ~r1_orders_2(sK0,k12_lattice3(sK0,sK1,sK2),sK2) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(k12_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | spl5_2),
% 1.48/0.54    inference(trivial_inequality_removal,[],[f163])).
% 1.48/0.54  fof(f163,plain,(
% 1.48/0.54    sK2 != sK2 | ~r1_orders_2(sK0,sK2,sK2) | ~r1_orders_2(sK0,k12_lattice3(sK0,sK1,sK2),sK2) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(k12_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | spl5_2),
% 1.48/0.54    inference(superposition,[],[f114,f138])).
% 1.48/0.54  fof(f138,plain,(
% 1.48/0.54    ( ! [X2,X0,X1] : (k10_lattice3(X0,X1,X2) = X2 | ~r1_orders_2(X0,X2,X2) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 1.48/0.54    inference(duplicate_literal_removal,[],[f137])).
% 1.48/0.54  fof(f137,plain,(
% 1.48/0.54    ( ! [X2,X0,X1] : (k10_lattice3(X0,X1,X2) = X2 | ~r1_orders_2(X0,X2,X2) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | k10_lattice3(X0,X1,X2) = X2 | ~r1_orders_2(X0,X2,X2) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 1.48/0.54    inference(resolution,[],[f78,f77])).
% 1.48/0.54  fof(f77,plain,(
% 1.48/0.54    ( ! [X2,X0,X3,X1] : (~r1_orders_2(X0,X3,sK3(X0,X1,X2,X3)) | k10_lattice3(X0,X1,X2) = X3 | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 1.48/0.54    inference(subsumption_resolution,[],[f60,f51])).
% 1.48/0.54  fof(f60,plain,(
% 1.48/0.54    ( ! [X2,X0,X3,X1] : (k10_lattice3(X0,X1,X2) = X3 | ~r1_orders_2(X0,X3,sK3(X0,X1,X2,X3)) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 1.48/0.54    inference(cnf_transformation,[],[f37])).
% 1.48/0.54  fof(f37,plain,(
% 1.48/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,X3,sK3(X0,X1,X2,X3)) & r1_orders_2(X0,X2,sK3(X0,X1,X2,X3)) & r1_orders_2(X0,X1,sK3(X0,X1,X2,X3)) & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.48/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f36])).
% 1.48/0.54  fof(f36,plain,(
% 1.48/0.54    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,X3,sK3(X0,X1,X2,X3)) & r1_orders_2(X0,X2,sK3(X0,X1,X2,X3)) & r1_orders_2(X0,X1,sK3(X0,X1,X2,X3)) & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0))))),
% 1.48/0.54    introduced(choice_axiom,[])).
% 1.48/0.54  fof(f35,plain,(
% 1.48/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.48/0.54    inference(rectify,[],[f34])).
% 1.48/0.54  fof(f34,plain,(
% 1.48/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.48/0.54    inference(flattening,[],[f33])).
% 1.48/0.54  fof(f33,plain,(
% 1.48/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3))) & ((! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.48/0.54    inference(nnf_transformation,[],[f20])).
% 1.48/0.54  fof(f20,plain,(
% 1.48/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.48/0.54    inference(flattening,[],[f19])).
% 1.48/0.54  fof(f19,plain,(
% 1.48/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X3,X4) | (~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 1.48/0.54    inference(ennf_transformation,[],[f5])).
% 1.48/0.54  fof(f5,axiom,(
% 1.48/0.54    ! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4)) => r1_orders_2(X0,X3,X4))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)))))))),
% 1.48/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l26_lattice3)).
% 1.48/0.54  fof(f78,plain,(
% 1.48/0.54    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X2,sK3(X0,X1,X2,X3)) | k10_lattice3(X0,X1,X2) = X3 | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 1.48/0.54    inference(subsumption_resolution,[],[f59,f51])).
% 1.48/0.54  fof(f59,plain,(
% 1.48/0.54    ( ! [X2,X0,X3,X1] : (k10_lattice3(X0,X1,X2) = X3 | r1_orders_2(X0,X2,sK3(X0,X1,X2,X3)) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 1.48/0.54    inference(cnf_transformation,[],[f37])).
% 1.48/0.54  fof(f114,plain,(
% 1.48/0.54    sK2 != k10_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2) | spl5_2),
% 1.48/0.54    inference(avatar_component_clause,[],[f113])).
% 1.48/0.54  fof(f136,plain,(
% 1.48/0.54    spl5_1),
% 1.48/0.54    inference(avatar_contradiction_clause,[],[f135])).
% 1.48/0.54  fof(f135,plain,(
% 1.48/0.54    $false | spl5_1),
% 1.48/0.54    inference(subsumption_resolution,[],[f134,f47])).
% 1.48/0.54  fof(f134,plain,(
% 1.48/0.54    ~l1_orders_2(sK0) | spl5_1),
% 1.48/0.54    inference(subsumption_resolution,[],[f133,f48])).
% 1.48/0.54  fof(f133,plain,(
% 1.48/0.54    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | spl5_1),
% 1.48/0.54    inference(subsumption_resolution,[],[f132,f49])).
% 1.48/0.54  fof(f132,plain,(
% 1.48/0.54    ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | spl5_1),
% 1.48/0.54    inference(resolution,[],[f127,f70])).
% 1.48/0.54  fof(f127,plain,(
% 1.48/0.54    ~m1_subset_1(k11_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | spl5_1),
% 1.48/0.54    inference(subsumption_resolution,[],[f126,f44])).
% 1.48/0.54  fof(f126,plain,(
% 1.48/0.54    ~m1_subset_1(k11_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | ~v5_orders_2(sK0) | spl5_1),
% 1.48/0.54    inference(subsumption_resolution,[],[f125,f46])).
% 1.48/0.54  fof(f125,plain,(
% 1.48/0.54    ~m1_subset_1(k11_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | ~v2_lattice3(sK0) | ~v5_orders_2(sK0) | spl5_1),
% 1.48/0.54    inference(subsumption_resolution,[],[f124,f47])).
% 1.48/0.54  fof(f124,plain,(
% 1.48/0.54    ~m1_subset_1(k11_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0) | ~v5_orders_2(sK0) | spl5_1),
% 1.48/0.54    inference(subsumption_resolution,[],[f123,f48])).
% 1.48/0.54  fof(f123,plain,(
% 1.48/0.54    ~m1_subset_1(k11_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0) | ~v5_orders_2(sK0) | spl5_1),
% 1.48/0.54    inference(subsumption_resolution,[],[f122,f49])).
% 1.48/0.54  fof(f122,plain,(
% 1.48/0.54    ~m1_subset_1(k11_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0) | ~v5_orders_2(sK0) | spl5_1),
% 1.48/0.54    inference(superposition,[],[f111,f69])).
% 1.48/0.54  fof(f111,plain,(
% 1.48/0.54    ~m1_subset_1(k12_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | spl5_1),
% 1.48/0.54    inference(avatar_component_clause,[],[f110])).
% 1.48/0.54  fof(f115,plain,(
% 1.48/0.54    ~spl5_1 | ~spl5_2),
% 1.48/0.54    inference(avatar_split_clause,[],[f108,f113,f110])).
% 1.48/0.54  fof(f108,plain,(
% 1.48/0.54    sK2 != k10_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2) | ~m1_subset_1(k12_lattice3(sK0,sK1,sK2),u1_struct_0(sK0))),
% 1.48/0.54    inference(subsumption_resolution,[],[f107,f44])).
% 1.48/0.54  fof(f107,plain,(
% 1.48/0.54    sK2 != k10_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2) | ~m1_subset_1(k12_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | ~v5_orders_2(sK0)),
% 1.48/0.54    inference(subsumption_resolution,[],[f106,f45])).
% 1.48/0.54  fof(f106,plain,(
% 1.48/0.54    sK2 != k10_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2) | ~m1_subset_1(k12_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0)),
% 1.48/0.54    inference(subsumption_resolution,[],[f105,f47])).
% 1.48/0.54  fof(f105,plain,(
% 1.48/0.54    sK2 != k10_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2) | ~m1_subset_1(k12_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0)),
% 1.48/0.54    inference(subsumption_resolution,[],[f104,f49])).
% 1.48/0.54  fof(f104,plain,(
% 1.48/0.54    sK2 != k10_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(k12_lattice3(sK0,sK1,sK2),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0)),
% 1.48/0.54    inference(superposition,[],[f50,f68])).
% 1.48/0.54  fof(f68,plain,(
% 1.48/0.54    ( ! [X2,X0,X1] : (k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 1.48/0.54    inference(cnf_transformation,[],[f24])).
% 1.48/0.54  fof(f24,plain,(
% 1.48/0.54    ! [X0,X1,X2] : (k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 1.48/0.54    inference(flattening,[],[f23])).
% 1.48/0.54  fof(f23,plain,(
% 1.48/0.54    ! [X0,X1,X2] : (k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 1.48/0.54    inference(ennf_transformation,[],[f8])).
% 1.48/0.54  fof(f8,axiom,(
% 1.48/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => k10_lattice3(X0,X1,X2) = k13_lattice3(X0,X1,X2))),
% 1.48/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k13_lattice3)).
% 1.48/0.54  fof(f50,plain,(
% 1.48/0.54    sK2 != k13_lattice3(sK0,k12_lattice3(sK0,sK1,sK2),sK2)),
% 1.48/0.54    inference(cnf_transformation,[],[f32])).
% 1.48/0.54  % SZS output end Proof for theBenchmark
% 1.48/0.54  % (11262)------------------------------
% 1.48/0.54  % (11262)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.54  % (11262)Termination reason: Refutation
% 1.48/0.54  
% 1.48/0.54  % (11262)Memory used [KB]: 10746
% 1.48/0.54  % (11262)Time elapsed: 0.113 s
% 1.48/0.54  % (11262)------------------------------
% 1.48/0.54  % (11262)------------------------------
% 1.48/0.54  % (11261)Refutation not found, incomplete strategy% (11261)------------------------------
% 1.48/0.54  % (11261)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.54  % (11261)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.54  
% 1.48/0.54  % (11261)Memory used [KB]: 10618
% 1.48/0.54  % (11261)Time elapsed: 0.134 s
% 1.48/0.54  % (11261)------------------------------
% 1.48/0.54  % (11261)------------------------------
% 1.48/0.55  % (11280)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 1.48/0.55  % (11259)Success in time 0.187 s
%------------------------------------------------------------------------------
