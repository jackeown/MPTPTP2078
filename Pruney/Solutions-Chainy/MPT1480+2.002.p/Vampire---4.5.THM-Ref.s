%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:33 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 226 expanded)
%              Number of leaves         :    8 (  55 expanded)
%              Depth                    :   31
%              Number of atoms          :  611 (2028 expanded)
%              Number of equality atoms :   50 ( 183 expanded)
%              Maximal formula depth    :   25 (  11 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f281,plain,(
    $false ),
    inference(subsumption_resolution,[],[f280,f26])).

fof(f26,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( k10_lattice3(sK0,sK1,sK2) != k10_lattice3(sK0,sK2,sK1)
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v1_lattice3(sK0)
    & v5_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f16,f15,f14])).

fof(f14,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k10_lattice3(X0,X1,X2) != k10_lattice3(X0,X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k10_lattice3(sK0,X1,X2) != k10_lattice3(sK0,X2,X1)
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v1_lattice3(sK0)
      & v5_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k10_lattice3(sK0,X1,X2) != k10_lattice3(sK0,X2,X1)
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( k10_lattice3(sK0,sK1,X2) != k10_lattice3(sK0,X2,sK1)
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X2] :
        ( k10_lattice3(sK0,sK1,X2) != k10_lattice3(sK0,X2,sK1)
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( k10_lattice3(sK0,sK1,sK2) != k10_lattice3(sK0,sK2,sK1)
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k10_lattice3(X0,X1,X2) != k10_lattice3(X0,X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k10_lattice3(X0,X1,X2) != k10_lattice3(X0,X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X1) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_lattice3)).

fof(f280,plain,(
    ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f279,f23])).

fof(f23,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f279,plain,
    ( ~ v5_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f278,f24])).

fof(f24,plain,(
    v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f278,plain,
    ( ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f277,f25])).

fof(f25,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f277,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f272,f27])).

fof(f27,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f272,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(trivial_inequality_removal,[],[f213])).

fof(f213,plain,
    ( k10_lattice3(sK0,sK1,sK2) != k10_lattice3(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(superposition,[],[f28,f205])).

fof(f205,plain,(
    ! [X2,X0,X1] :
      ( k10_lattice3(X1,X2,X0) = k10_lattice3(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f204,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_lattice3)).

fof(f204,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | k10_lattice3(X1,X2,X0) = k10_lattice3(X1,X0,X2)
      | ~ m1_subset_1(k10_lattice3(X1,X2,X0),u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f203,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,k10_lattice3(X0,X2,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,k10_lattice3(X0,X2,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f46,f37])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | r1_orders_2(X0,X2,k10_lattice3(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f39,f29])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
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

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X2,k10_lattice3(X0,X1,X2))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
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
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f21])).

fof(f21,plain,(
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

fof(f20,plain,(
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
    inference(rectify,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f203,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | k10_lattice3(X1,X2,X0) = k10_lattice3(X1,X0,X2)
      | ~ r1_orders_2(X1,X0,k10_lattice3(X1,X2,X0))
      | ~ m1_subset_1(k10_lattice3(X1,X2,X0),u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f202,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f47,f37])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f40,f29])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
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
    inference(cnf_transformation,[],[f22])).

fof(f202,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | k10_lattice3(X1,X2,X0) = k10_lattice3(X1,X0,X2)
      | ~ r1_orders_2(X1,X2,k10_lattice3(X1,X2,X0))
      | ~ r1_orders_2(X1,X0,k10_lattice3(X1,X2,X0))
      | ~ m1_subset_1(k10_lattice3(X1,X2,X0),u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f193])).

fof(f193,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | k10_lattice3(X1,X2,X0) = k10_lattice3(X1,X0,X2)
      | ~ r1_orders_2(X1,X2,k10_lattice3(X1,X2,X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | k10_lattice3(X1,X2,X0) = k10_lattice3(X1,X0,X2)
      | ~ r1_orders_2(X1,X2,k10_lattice3(X1,X2,X0))
      | ~ r1_orders_2(X1,X0,k10_lattice3(X1,X2,X0))
      | ~ m1_subset_1(k10_lattice3(X1,X2,X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1) ) ),
    inference(resolution,[],[f144,f42])).

fof(f42,plain,(
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
    inference(subsumption_resolution,[],[f35,f29])).

fof(f35,plain,(
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
    inference(cnf_transformation,[],[f22])).

fof(f144,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,X5,sK3(X4,X6,X7,k10_lattice3(X4,X5,X6)))
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v1_lattice3(X4)
      | ~ v5_orders_2(X4)
      | k10_lattice3(X4,X5,X6) = k10_lattice3(X4,X6,X7)
      | ~ r1_orders_2(X4,X7,k10_lattice3(X4,X5,X6))
      | ~ m1_subset_1(X7,u1_struct_0(X4)) ) ),
    inference(subsumption_resolution,[],[f143,f37])).

fof(f143,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,X5,sK3(X4,X6,X7,k10_lattice3(X4,X5,X6)))
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v1_lattice3(X4)
      | ~ v5_orders_2(X4)
      | k10_lattice3(X4,X5,X6) = k10_lattice3(X4,X6,X7)
      | ~ r1_orders_2(X4,X7,k10_lattice3(X4,X5,X6))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(k10_lattice3(X4,X5,X6),u1_struct_0(X4)) ) ),
    inference(subsumption_resolution,[],[f139,f49])).

fof(f139,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,X5,sK3(X4,X6,X7,k10_lattice3(X4,X5,X6)))
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v1_lattice3(X4)
      | ~ v5_orders_2(X4)
      | k10_lattice3(X4,X5,X6) = k10_lattice3(X4,X6,X7)
      | ~ r1_orders_2(X4,X7,k10_lattice3(X4,X5,X6))
      | ~ r1_orders_2(X4,X6,k10_lattice3(X4,X5,X6))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(k10_lattice3(X4,X5,X6),u1_struct_0(X4)) ) ),
    inference(duplicate_literal_removal,[],[f132])).

fof(f132,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,X5,sK3(X4,X6,X7,k10_lattice3(X4,X5,X6)))
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v1_lattice3(X4)
      | ~ v5_orders_2(X4)
      | k10_lattice3(X4,X5,X6) = k10_lattice3(X4,X6,X7)
      | ~ r1_orders_2(X4,X7,k10_lattice3(X4,X5,X6))
      | ~ r1_orders_2(X4,X6,k10_lattice3(X4,X5,X6))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | k10_lattice3(X4,X5,X6) = k10_lattice3(X4,X6,X7)
      | ~ r1_orders_2(X4,X7,k10_lattice3(X4,X5,X6))
      | ~ r1_orders_2(X4,X6,k10_lattice3(X4,X5,X6))
      | ~ m1_subset_1(k10_lattice3(X4,X5,X6),u1_struct_0(X4))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v1_lattice3(X4)
      | ~ v5_orders_2(X4) ) ),
    inference(resolution,[],[f125,f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,sK3(X0,X1,X2,X3))
      | k10_lattice3(X0,X1,X2) = X3
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f34,f29])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_lattice3(X0,X1,X2) = X3
      | r1_orders_2(X0,X1,sK3(X0,X1,X2,X3))
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f125,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,X4,sK3(X0,X2,X3,k10_lattice3(X0,X1,X4)))
      | ~ r1_orders_2(X0,X1,sK3(X0,X2,X3,k10_lattice3(X0,X1,X4)))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | k10_lattice3(X0,X1,X4) = k10_lattice3(X0,X2,X3)
      | ~ r1_orders_2(X0,X3,k10_lattice3(X0,X1,X4))
      | ~ r1_orders_2(X0,X2,k10_lattice3(X0,X1,X4))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f124,f37])).

fof(f124,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,X1,sK3(X0,X2,X3,k10_lattice3(X0,X1,X4)))
      | ~ r1_orders_2(X0,X4,sK3(X0,X2,X3,k10_lattice3(X0,X1,X4)))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | k10_lattice3(X0,X1,X4) = k10_lattice3(X0,X2,X3)
      | ~ r1_orders_2(X0,X3,k10_lattice3(X0,X1,X4))
      | ~ r1_orders_2(X0,X2,k10_lattice3(X0,X1,X4))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X4),u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f123,f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0))
      | k10_lattice3(X0,X1,X2) = X3
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f33,f29])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_lattice3(X0,X1,X2) = X3
      | m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0))
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f123,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,X1,sK3(X0,X2,X3,k10_lattice3(X0,X1,X4)))
      | ~ m1_subset_1(sK3(X0,X2,X3,k10_lattice3(X0,X1,X4)),u1_struct_0(X0))
      | ~ r1_orders_2(X0,X4,sK3(X0,X2,X3,k10_lattice3(X0,X1,X4)))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | k10_lattice3(X0,X1,X4) = k10_lattice3(X0,X2,X3)
      | ~ r1_orders_2(X0,X3,k10_lattice3(X0,X1,X4))
      | ~ r1_orders_2(X0,X2,k10_lattice3(X0,X1,X4))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X4),u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f118])).

fof(f118,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,X1,sK3(X0,X2,X3,k10_lattice3(X0,X1,X4)))
      | ~ m1_subset_1(sK3(X0,X2,X3,k10_lattice3(X0,X1,X4)),u1_struct_0(X0))
      | ~ r1_orders_2(X0,X4,sK3(X0,X2,X3,k10_lattice3(X0,X1,X4)))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | k10_lattice3(X0,X1,X4) = k10_lattice3(X0,X2,X3)
      | ~ r1_orders_2(X0,X3,k10_lattice3(X0,X1,X4))
      | ~ r1_orders_2(X0,X2,k10_lattice3(X0,X1,X4))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X4),u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(resolution,[],[f85,f41])).

fof(f41,plain,(
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
    inference(subsumption_resolution,[],[f36,f29])).

fof(f36,plain,(
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
    inference(cnf_transformation,[],[f22])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,k10_lattice3(X0,X3,X1),X2)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f82])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_orders_2(X0,k10_lattice3(X0,X3,X1),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f45,f37])).

fof(f45,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ r1_orders_2(X0,X2,X5)
      | ~ r1_orders_2(X0,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | r1_orders_2(X0,k10_lattice3(X0,X1,X2),X5)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f38,f29])).

% (11642)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f38,plain,(
    ! [X2,X0,X5,X1] :
      ( r1_orders_2(X0,k10_lattice3(X0,X1,X2),X5)
      | ~ r1_orders_2(X0,X2,X5)
      | ~ r1_orders_2(X0,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_orders_2(X0,X3,X5)
      | ~ r1_orders_2(X0,X2,X5)
      | ~ r1_orders_2(X0,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | k10_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f28,plain,(
    k10_lattice3(sK0,sK1,sK2) != k10_lattice3(sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : run_vampire %s %d
% 0.16/0.36  % Computer   : n008.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.36  % CPULimit   : 60
% 0.16/0.36  % WCLimit    : 600
% 0.16/0.36  % DateTime   : Tue Dec  1 10:19:45 EST 2020
% 0.16/0.36  % CPUTime    : 
% 0.24/0.48  % (11647)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.24/0.48  % (11655)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.24/0.48  % (11651)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.24/0.49  % (11639)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.24/0.49  % (11643)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.24/0.50  % (11654)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.24/0.50  % (11639)Refutation found. Thanks to Tanya!
% 0.24/0.50  % SZS status Theorem for theBenchmark
% 0.24/0.50  % SZS output start Proof for theBenchmark
% 0.24/0.50  fof(f281,plain,(
% 0.24/0.50    $false),
% 0.24/0.50    inference(subsumption_resolution,[],[f280,f26])).
% 0.24/0.50  fof(f26,plain,(
% 0.24/0.50    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.24/0.50    inference(cnf_transformation,[],[f17])).
% 0.24/0.50  fof(f17,plain,(
% 0.24/0.50    ((k10_lattice3(sK0,sK1,sK2) != k10_lattice3(sK0,sK2,sK1) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v1_lattice3(sK0) & v5_orders_2(sK0)),
% 0.24/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f16,f15,f14])).
% 0.24/0.50  fof(f14,plain,(
% 0.24/0.50    ? [X0] : (? [X1] : (? [X2] : (k10_lattice3(X0,X1,X2) != k10_lattice3(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => (? [X1] : (? [X2] : (k10_lattice3(sK0,X1,X2) != k10_lattice3(sK0,X2,X1) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v1_lattice3(sK0) & v5_orders_2(sK0))),
% 0.24/0.50    introduced(choice_axiom,[])).
% 0.24/0.50  fof(f15,plain,(
% 0.24/0.50    ? [X1] : (? [X2] : (k10_lattice3(sK0,X1,X2) != k10_lattice3(sK0,X2,X1) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (k10_lattice3(sK0,sK1,X2) != k10_lattice3(sK0,X2,sK1) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.24/0.50    introduced(choice_axiom,[])).
% 0.24/0.50  fof(f16,plain,(
% 0.24/0.50    ? [X2] : (k10_lattice3(sK0,sK1,X2) != k10_lattice3(sK0,X2,sK1) & m1_subset_1(X2,u1_struct_0(sK0))) => (k10_lattice3(sK0,sK1,sK2) != k10_lattice3(sK0,sK2,sK1) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 0.24/0.50    introduced(choice_axiom,[])).
% 0.24/0.50  fof(f7,plain,(
% 0.24/0.50    ? [X0] : (? [X1] : (? [X2] : (k10_lattice3(X0,X1,X2) != k10_lattice3(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0))),
% 0.24/0.50    inference(flattening,[],[f6])).
% 0.24/0.50  fof(f6,plain,(
% 0.24/0.50    ? [X0] : (? [X1] : (? [X2] : (k10_lattice3(X0,X1,X2) != k10_lattice3(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)))),
% 0.24/0.50    inference(ennf_transformation,[],[f5])).
% 0.24/0.50  fof(f5,negated_conjecture,(
% 0.24/0.50    ~! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X1))))),
% 0.24/0.50    inference(negated_conjecture,[],[f4])).
% 0.24/0.50  fof(f4,conjecture,(
% 0.24/0.50    ! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X1))))),
% 0.24/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_lattice3)).
% 0.24/0.50  fof(f280,plain,(
% 0.24/0.50    ~m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.24/0.50    inference(subsumption_resolution,[],[f279,f23])).
% 0.24/0.50  fof(f23,plain,(
% 0.24/0.50    v5_orders_2(sK0)),
% 0.24/0.50    inference(cnf_transformation,[],[f17])).
% 0.24/0.50  fof(f279,plain,(
% 0.24/0.50    ~v5_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.24/0.50    inference(subsumption_resolution,[],[f278,f24])).
% 0.24/0.50  fof(f24,plain,(
% 0.24/0.50    v1_lattice3(sK0)),
% 0.24/0.50    inference(cnf_transformation,[],[f17])).
% 0.24/0.50  fof(f278,plain,(
% 0.24/0.50    ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.24/0.50    inference(subsumption_resolution,[],[f277,f25])).
% 0.24/0.50  fof(f25,plain,(
% 0.24/0.50    l1_orders_2(sK0)),
% 0.24/0.50    inference(cnf_transformation,[],[f17])).
% 0.24/0.50  fof(f277,plain,(
% 0.24/0.50    ~l1_orders_2(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.24/0.50    inference(subsumption_resolution,[],[f272,f27])).
% 0.24/0.50  fof(f27,plain,(
% 0.24/0.50    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.24/0.50    inference(cnf_transformation,[],[f17])).
% 0.24/0.50  fof(f272,plain,(
% 0.24/0.50    ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.24/0.50    inference(trivial_inequality_removal,[],[f213])).
% 0.24/0.50  fof(f213,plain,(
% 0.24/0.50    k10_lattice3(sK0,sK1,sK2) != k10_lattice3(sK0,sK1,sK2) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v1_lattice3(sK0) | ~v5_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.24/0.50    inference(superposition,[],[f28,f205])).
% 0.24/0.50  fof(f205,plain,(
% 0.24/0.50    ( ! [X2,X0,X1] : (k10_lattice3(X1,X2,X0) = k10_lattice3(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_orders_2(X1) | ~v1_lattice3(X1) | ~v5_orders_2(X1) | ~m1_subset_1(X0,u1_struct_0(X1))) )),
% 0.24/0.50    inference(subsumption_resolution,[],[f204,f37])).
% 0.24/0.50  fof(f37,plain,(
% 0.24/0.50    ( ! [X2,X0,X1] : (m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.24/0.50    inference(cnf_transformation,[],[f13])).
% 0.24/0.50  fof(f13,plain,(
% 0.24/0.50    ! [X0,X1,X2] : (m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 0.24/0.50    inference(flattening,[],[f12])).
% 0.24/0.50  fof(f12,plain,(
% 0.24/0.50    ! [X0,X1,X2] : (m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)))),
% 0.24/0.50    inference(ennf_transformation,[],[f2])).
% 0.24/0.50  fof(f2,axiom,(
% 0.24/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0)) => m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)))),
% 0.24/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_lattice3)).
% 0.24/0.50  fof(f204,plain,(
% 0.24/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_orders_2(X1) | ~v1_lattice3(X1) | ~v5_orders_2(X1) | k10_lattice3(X1,X2,X0) = k10_lattice3(X1,X0,X2) | ~m1_subset_1(k10_lattice3(X1,X2,X0),u1_struct_0(X1))) )),
% 0.24/0.50    inference(subsumption_resolution,[],[f203,f49])).
% 0.24/0.50  fof(f49,plain,(
% 0.24/0.50    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,k10_lattice3(X0,X2,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.24/0.50    inference(duplicate_literal_removal,[],[f48])).
% 0.24/0.50  fof(f48,plain,(
% 0.24/0.50    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,k10_lattice3(X0,X2,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.24/0.50    inference(resolution,[],[f46,f37])).
% 0.24/0.50  fof(f46,plain,(
% 0.24/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | r1_orders_2(X0,X2,k10_lattice3(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.24/0.50    inference(subsumption_resolution,[],[f39,f29])).
% 0.24/0.50  fof(f29,plain,(
% 0.24/0.50    ( ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0)) )),
% 0.24/0.50    inference(cnf_transformation,[],[f9])).
% 0.24/0.50  fof(f9,plain,(
% 0.24/0.50    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 0.24/0.50    inference(flattening,[],[f8])).
% 0.24/0.50  fof(f8,plain,(
% 0.24/0.50    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 0.24/0.50    inference(ennf_transformation,[],[f1])).
% 0.24/0.50  fof(f1,axiom,(
% 0.24/0.50    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 0.24/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).
% 0.24/0.50  fof(f39,plain,(
% 0.24/0.50    ( ! [X2,X0,X1] : (r1_orders_2(X0,X2,k10_lattice3(X0,X1,X2)) | ~m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.24/0.50    inference(equality_resolution,[],[f31])).
% 0.24/0.50  fof(f31,plain,(
% 0.24/0.50    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X2,X3) | k10_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.24/0.50    inference(cnf_transformation,[],[f22])).
% 0.24/0.51  fof(f22,plain,(
% 0.24/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,X3,sK3(X0,X1,X2,X3)) & r1_orders_2(X0,X2,sK3(X0,X1,X2,X3)) & r1_orders_2(X0,X1,sK3(X0,X1,X2,X3)) & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.24/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f21])).
% 0.24/0.51  fof(f21,plain,(
% 0.24/0.51    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,X3,sK3(X0,X1,X2,X3)) & r1_orders_2(X0,X2,sK3(X0,X1,X2,X3)) & r1_orders_2(X0,X1,sK3(X0,X1,X2,X3)) & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0))))),
% 0.24/0.51    introduced(choice_axiom,[])).
% 0.24/0.51  fof(f20,plain,(
% 0.24/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.24/0.51    inference(rectify,[],[f19])).
% 0.24/0.51  fof(f19,plain,(
% 0.24/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.24/0.51    inference(flattening,[],[f18])).
% 0.24/0.51  fof(f18,plain,(
% 0.24/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3))) & ((! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.24/0.51    inference(nnf_transformation,[],[f11])).
% 0.24/0.51  fof(f11,plain,(
% 0.24/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.24/0.51    inference(flattening,[],[f10])).
% 0.24/0.51  fof(f10,plain,(
% 0.24/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X3,X4) | (~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 0.24/0.51    inference(ennf_transformation,[],[f3])).
% 0.24/0.51  fof(f3,axiom,(
% 0.24/0.51    ! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4)) => r1_orders_2(X0,X3,X4))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)))))))),
% 0.24/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l26_lattice3)).
% 0.24/0.51  fof(f203,plain,(
% 0.24/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_orders_2(X1) | ~v1_lattice3(X1) | ~v5_orders_2(X1) | k10_lattice3(X1,X2,X0) = k10_lattice3(X1,X0,X2) | ~r1_orders_2(X1,X0,k10_lattice3(X1,X2,X0)) | ~m1_subset_1(k10_lattice3(X1,X2,X0),u1_struct_0(X1))) )),
% 0.24/0.51    inference(subsumption_resolution,[],[f202,f51])).
% 0.24/0.51  fof(f51,plain,(
% 0.24/0.51    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.24/0.51    inference(duplicate_literal_removal,[],[f50])).
% 0.24/0.51  fof(f50,plain,(
% 0.24/0.51    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.24/0.51    inference(resolution,[],[f47,f37])).
% 0.24/0.51  fof(f47,plain,(
% 0.24/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.24/0.51    inference(subsumption_resolution,[],[f40,f29])).
% 0.24/0.51  fof(f40,plain,(
% 0.24/0.51    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2)) | ~m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.24/0.51    inference(equality_resolution,[],[f30])).
% 0.24/0.51  fof(f30,plain,(
% 0.24/0.51    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X1,X3) | k10_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.24/0.51    inference(cnf_transformation,[],[f22])).
% 0.24/0.51  fof(f202,plain,(
% 0.24/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_orders_2(X1) | ~v1_lattice3(X1) | ~v5_orders_2(X1) | k10_lattice3(X1,X2,X0) = k10_lattice3(X1,X0,X2) | ~r1_orders_2(X1,X2,k10_lattice3(X1,X2,X0)) | ~r1_orders_2(X1,X0,k10_lattice3(X1,X2,X0)) | ~m1_subset_1(k10_lattice3(X1,X2,X0),u1_struct_0(X1))) )),
% 0.24/0.51    inference(duplicate_literal_removal,[],[f193])).
% 0.24/0.51  fof(f193,plain,(
% 0.24/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_orders_2(X1) | ~v1_lattice3(X1) | ~v5_orders_2(X1) | k10_lattice3(X1,X2,X0) = k10_lattice3(X1,X0,X2) | ~r1_orders_2(X1,X2,k10_lattice3(X1,X2,X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | k10_lattice3(X1,X2,X0) = k10_lattice3(X1,X0,X2) | ~r1_orders_2(X1,X2,k10_lattice3(X1,X2,X0)) | ~r1_orders_2(X1,X0,k10_lattice3(X1,X2,X0)) | ~m1_subset_1(k10_lattice3(X1,X2,X0),u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_orders_2(X1) | ~v1_lattice3(X1) | ~v5_orders_2(X1)) )),
% 0.24/0.51    inference(resolution,[],[f144,f42])).
% 0.24/0.51  fof(f42,plain,(
% 0.24/0.51    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X2,sK3(X0,X1,X2,X3)) | k10_lattice3(X0,X1,X2) = X3 | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.24/0.51    inference(subsumption_resolution,[],[f35,f29])).
% 0.24/0.51  fof(f35,plain,(
% 0.24/0.51    ( ! [X2,X0,X3,X1] : (k10_lattice3(X0,X1,X2) = X3 | r1_orders_2(X0,X2,sK3(X0,X1,X2,X3)) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.24/0.51    inference(cnf_transformation,[],[f22])).
% 0.24/0.51  fof(f144,plain,(
% 0.24/0.51    ( ! [X6,X4,X7,X5] : (~r1_orders_2(X4,X5,sK3(X4,X6,X7,k10_lattice3(X4,X5,X6))) | ~m1_subset_1(X6,u1_struct_0(X4)) | ~m1_subset_1(X5,u1_struct_0(X4)) | ~l1_orders_2(X4) | ~v1_lattice3(X4) | ~v5_orders_2(X4) | k10_lattice3(X4,X5,X6) = k10_lattice3(X4,X6,X7) | ~r1_orders_2(X4,X7,k10_lattice3(X4,X5,X6)) | ~m1_subset_1(X7,u1_struct_0(X4))) )),
% 0.24/0.51    inference(subsumption_resolution,[],[f143,f37])).
% 0.24/0.51  fof(f143,plain,(
% 0.24/0.51    ( ! [X6,X4,X7,X5] : (~r1_orders_2(X4,X5,sK3(X4,X6,X7,k10_lattice3(X4,X5,X6))) | ~m1_subset_1(X6,u1_struct_0(X4)) | ~m1_subset_1(X5,u1_struct_0(X4)) | ~l1_orders_2(X4) | ~v1_lattice3(X4) | ~v5_orders_2(X4) | k10_lattice3(X4,X5,X6) = k10_lattice3(X4,X6,X7) | ~r1_orders_2(X4,X7,k10_lattice3(X4,X5,X6)) | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(k10_lattice3(X4,X5,X6),u1_struct_0(X4))) )),
% 0.24/0.51    inference(subsumption_resolution,[],[f139,f49])).
% 0.24/0.51  fof(f139,plain,(
% 0.24/0.51    ( ! [X6,X4,X7,X5] : (~r1_orders_2(X4,X5,sK3(X4,X6,X7,k10_lattice3(X4,X5,X6))) | ~m1_subset_1(X6,u1_struct_0(X4)) | ~m1_subset_1(X5,u1_struct_0(X4)) | ~l1_orders_2(X4) | ~v1_lattice3(X4) | ~v5_orders_2(X4) | k10_lattice3(X4,X5,X6) = k10_lattice3(X4,X6,X7) | ~r1_orders_2(X4,X7,k10_lattice3(X4,X5,X6)) | ~r1_orders_2(X4,X6,k10_lattice3(X4,X5,X6)) | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(k10_lattice3(X4,X5,X6),u1_struct_0(X4))) )),
% 0.24/0.51    inference(duplicate_literal_removal,[],[f132])).
% 0.24/0.51  fof(f132,plain,(
% 0.24/0.51    ( ! [X6,X4,X7,X5] : (~r1_orders_2(X4,X5,sK3(X4,X6,X7,k10_lattice3(X4,X5,X6))) | ~m1_subset_1(X6,u1_struct_0(X4)) | ~m1_subset_1(X5,u1_struct_0(X4)) | ~l1_orders_2(X4) | ~v1_lattice3(X4) | ~v5_orders_2(X4) | k10_lattice3(X4,X5,X6) = k10_lattice3(X4,X6,X7) | ~r1_orders_2(X4,X7,k10_lattice3(X4,X5,X6)) | ~r1_orders_2(X4,X6,k10_lattice3(X4,X5,X6)) | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X6,u1_struct_0(X4)) | k10_lattice3(X4,X5,X6) = k10_lattice3(X4,X6,X7) | ~r1_orders_2(X4,X7,k10_lattice3(X4,X5,X6)) | ~r1_orders_2(X4,X6,k10_lattice3(X4,X5,X6)) | ~m1_subset_1(k10_lattice3(X4,X5,X6),u1_struct_0(X4)) | ~m1_subset_1(X7,u1_struct_0(X4)) | ~m1_subset_1(X6,u1_struct_0(X4)) | ~l1_orders_2(X4) | ~v1_lattice3(X4) | ~v5_orders_2(X4)) )),
% 0.24/0.51    inference(resolution,[],[f125,f43])).
% 0.24/0.51  fof(f43,plain,(
% 0.24/0.51    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X1,sK3(X0,X1,X2,X3)) | k10_lattice3(X0,X1,X2) = X3 | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.24/0.51    inference(subsumption_resolution,[],[f34,f29])).
% 0.24/0.51  fof(f34,plain,(
% 0.24/0.51    ( ! [X2,X0,X3,X1] : (k10_lattice3(X0,X1,X2) = X3 | r1_orders_2(X0,X1,sK3(X0,X1,X2,X3)) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.24/0.51    inference(cnf_transformation,[],[f22])).
% 0.24/0.51  fof(f125,plain,(
% 0.24/0.51    ( ! [X4,X2,X0,X3,X1] : (~r1_orders_2(X0,X4,sK3(X0,X2,X3,k10_lattice3(X0,X1,X4))) | ~r1_orders_2(X0,X1,sK3(X0,X2,X3,k10_lattice3(X0,X1,X4))) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | k10_lattice3(X0,X1,X4) = k10_lattice3(X0,X2,X3) | ~r1_orders_2(X0,X3,k10_lattice3(X0,X1,X4)) | ~r1_orders_2(X0,X2,k10_lattice3(X0,X1,X4)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0))) )),
% 0.24/0.51    inference(subsumption_resolution,[],[f124,f37])).
% 0.24/0.51  fof(f124,plain,(
% 0.24/0.51    ( ! [X4,X2,X0,X3,X1] : (~r1_orders_2(X0,X1,sK3(X0,X2,X3,k10_lattice3(X0,X1,X4))) | ~r1_orders_2(X0,X4,sK3(X0,X2,X3,k10_lattice3(X0,X1,X4))) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | k10_lattice3(X0,X1,X4) = k10_lattice3(X0,X2,X3) | ~r1_orders_2(X0,X3,k10_lattice3(X0,X1,X4)) | ~r1_orders_2(X0,X2,k10_lattice3(X0,X1,X4)) | ~m1_subset_1(k10_lattice3(X0,X1,X4),u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0))) )),
% 0.24/0.51    inference(subsumption_resolution,[],[f123,f44])).
% 0.24/0.51  fof(f44,plain,(
% 0.24/0.51    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0)) | k10_lattice3(X0,X1,X2) = X3 | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.24/0.51    inference(subsumption_resolution,[],[f33,f29])).
% 0.24/0.51  fof(f33,plain,(
% 0.24/0.51    ( ! [X2,X0,X3,X1] : (k10_lattice3(X0,X1,X2) = X3 | m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0)) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.24/0.51    inference(cnf_transformation,[],[f22])).
% 0.24/0.51  fof(f123,plain,(
% 0.24/0.51    ( ! [X4,X2,X0,X3,X1] : (~r1_orders_2(X0,X1,sK3(X0,X2,X3,k10_lattice3(X0,X1,X4))) | ~m1_subset_1(sK3(X0,X2,X3,k10_lattice3(X0,X1,X4)),u1_struct_0(X0)) | ~r1_orders_2(X0,X4,sK3(X0,X2,X3,k10_lattice3(X0,X1,X4))) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | k10_lattice3(X0,X1,X4) = k10_lattice3(X0,X2,X3) | ~r1_orders_2(X0,X3,k10_lattice3(X0,X1,X4)) | ~r1_orders_2(X0,X2,k10_lattice3(X0,X1,X4)) | ~m1_subset_1(k10_lattice3(X0,X1,X4),u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0))) )),
% 0.24/0.51    inference(duplicate_literal_removal,[],[f118])).
% 0.24/0.51  fof(f118,plain,(
% 0.24/0.51    ( ! [X4,X2,X0,X3,X1] : (~r1_orders_2(X0,X1,sK3(X0,X2,X3,k10_lattice3(X0,X1,X4))) | ~m1_subset_1(sK3(X0,X2,X3,k10_lattice3(X0,X1,X4)),u1_struct_0(X0)) | ~r1_orders_2(X0,X4,sK3(X0,X2,X3,k10_lattice3(X0,X1,X4))) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | k10_lattice3(X0,X1,X4) = k10_lattice3(X0,X2,X3) | ~r1_orders_2(X0,X3,k10_lattice3(X0,X1,X4)) | ~r1_orders_2(X0,X2,k10_lattice3(X0,X1,X4)) | ~m1_subset_1(k10_lattice3(X0,X1,X4),u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.24/0.51    inference(resolution,[],[f85,f41])).
% 0.24/0.51  fof(f41,plain,(
% 0.24/0.51    ( ! [X2,X0,X3,X1] : (~r1_orders_2(X0,X3,sK3(X0,X1,X2,X3)) | k10_lattice3(X0,X1,X2) = X3 | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.24/0.51    inference(subsumption_resolution,[],[f36,f29])).
% 0.24/0.51  fof(f36,plain,(
% 0.24/0.51    ( ! [X2,X0,X3,X1] : (k10_lattice3(X0,X1,X2) = X3 | ~r1_orders_2(X0,X3,sK3(X0,X1,X2,X3)) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.24/0.51    inference(cnf_transformation,[],[f22])).
% 0.24/0.51  fof(f85,plain,(
% 0.24/0.51    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,k10_lattice3(X0,X3,X1),X2) | ~r1_orders_2(X0,X3,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.24/0.51    inference(duplicate_literal_removal,[],[f82])).
% 0.24/0.51  fof(f82,plain,(
% 0.24/0.51    ( ! [X2,X0,X3,X1] : (~r1_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X3,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_orders_2(X0,k10_lattice3(X0,X3,X1),X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.24/0.51    inference(resolution,[],[f45,f37])).
% 0.24/0.51  fof(f45,plain,(
% 0.24/0.51    ( ! [X2,X0,X5,X1] : (~m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0)) | r1_orders_2(X0,k10_lattice3(X0,X1,X2),X5) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.24/0.51    inference(subsumption_resolution,[],[f38,f29])).
% 0.24/0.51  % (11642)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.24/0.51  fof(f38,plain,(
% 0.24/0.51    ( ! [X2,X0,X5,X1] : (r1_orders_2(X0,k10_lattice3(X0,X1,X2),X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.24/0.51    inference(equality_resolution,[],[f32])).
% 0.24/0.51  fof(f32,plain,(
% 0.24/0.51    ( ! [X2,X0,X5,X3,X1] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0)) | k10_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.24/0.51    inference(cnf_transformation,[],[f22])).
% 0.24/0.51  fof(f28,plain,(
% 0.24/0.51    k10_lattice3(sK0,sK1,sK2) != k10_lattice3(sK0,sK2,sK1)),
% 0.24/0.51    inference(cnf_transformation,[],[f17])).
% 0.24/0.51  % SZS output end Proof for theBenchmark
% 0.24/0.51  % (11639)------------------------------
% 0.24/0.51  % (11639)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.24/0.51  % (11639)Termination reason: Refutation
% 0.24/0.51  
% 0.24/0.51  % (11639)Memory used [KB]: 10746
% 0.24/0.51  % (11639)Time elapsed: 0.077 s
% 0.24/0.51  % (11639)------------------------------
% 0.24/0.51  % (11639)------------------------------
% 0.24/0.51  % (11636)Success in time 0.136 s
%------------------------------------------------------------------------------
