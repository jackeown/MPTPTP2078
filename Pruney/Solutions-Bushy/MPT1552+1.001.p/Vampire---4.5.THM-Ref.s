%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1552+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:05 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  102 (5216 expanded)
%              Number of leaves         :   10 (2009 expanded)
%              Depth                    :   34
%              Number of atoms          :  617 (72515 expanded)
%              Number of equality atoms :   70 (8984 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f288,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f254,f244,f265,f243])).

fof(f243,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,sK1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,sK2,X0) ) ),
    inference(subsumption_resolution,[],[f242,f28])).

fof(f28,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ( ( ( ~ r1_yellow_0(sK0,sK2)
          | sK1 != k1_yellow_0(sK0,sK2) )
        & ! [X3] :
            ( r1_orders_2(sK0,sK1,X3)
            | ~ r2_lattice3(sK0,sK2,X3)
            | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
        & r2_lattice3(sK0,sK2,sK1) )
      | ( ( ( ~ r1_orders_2(sK0,sK1,sK3)
            & r2_lattice3(sK0,sK2,sK3)
            & m1_subset_1(sK3,u1_struct_0(sK0)) )
          | ~ r2_lattice3(sK0,sK2,sK1) )
        & r1_yellow_0(sK0,sK2)
        & sK1 = k1_yellow_0(sK0,sK2) ) )
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f15,f14,f13,f12])).

fof(f12,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ( ~ r1_yellow_0(X0,X2)
                    | k1_yellow_0(X0,X2) != X1 )
                  & ! [X3] :
                      ( r1_orders_2(X0,X1,X3)
                      | ~ r2_lattice3(X0,X2,X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | ( ( ? [X4] :
                        ( ~ r1_orders_2(X0,X1,X4)
                        & r2_lattice3(X0,X2,X4)
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ r2_lattice3(X0,X2,X1) )
                  & r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 ) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ( ~ r1_yellow_0(sK0,X2)
                  | k1_yellow_0(sK0,X2) != X1 )
                & ! [X3] :
                    ( r1_orders_2(sK0,X1,X3)
                    | ~ r2_lattice3(sK0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
                & r2_lattice3(sK0,X2,X1) )
              | ( ( ? [X4] :
                      ( ~ r1_orders_2(sK0,X1,X4)
                      & r2_lattice3(sK0,X2,X4)
                      & m1_subset_1(X4,u1_struct_0(sK0)) )
                  | ~ r2_lattice3(sK0,X2,X1) )
                & r1_yellow_0(sK0,X2)
                & k1_yellow_0(sK0,X2) = X1 ) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ( ~ r1_yellow_0(sK0,X2)
                | k1_yellow_0(sK0,X2) != X1 )
              & ! [X3] :
                  ( r1_orders_2(sK0,X1,X3)
                  | ~ r2_lattice3(sK0,X2,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
              & r2_lattice3(sK0,X2,X1) )
            | ( ( ? [X4] :
                    ( ~ r1_orders_2(sK0,X1,X4)
                    & r2_lattice3(sK0,X2,X4)
                    & m1_subset_1(X4,u1_struct_0(sK0)) )
                | ~ r2_lattice3(sK0,X2,X1) )
              & r1_yellow_0(sK0,X2)
              & k1_yellow_0(sK0,X2) = X1 ) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ( ( ~ r1_yellow_0(sK0,X2)
              | k1_yellow_0(sK0,X2) != sK1 )
            & ! [X3] :
                ( r1_orders_2(sK0,sK1,X3)
                | ~ r2_lattice3(sK0,X2,X3)
                | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
            & r2_lattice3(sK0,X2,sK1) )
          | ( ( ? [X4] :
                  ( ~ r1_orders_2(sK0,sK1,X4)
                  & r2_lattice3(sK0,X2,X4)
                  & m1_subset_1(X4,u1_struct_0(sK0)) )
              | ~ r2_lattice3(sK0,X2,sK1) )
            & r1_yellow_0(sK0,X2)
            & k1_yellow_0(sK0,X2) = sK1 ) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ? [X2] :
        ( ( ( ~ r1_yellow_0(sK0,X2)
            | k1_yellow_0(sK0,X2) != sK1 )
          & ! [X3] :
              ( r1_orders_2(sK0,sK1,X3)
              | ~ r2_lattice3(sK0,X2,X3)
              | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
          & r2_lattice3(sK0,X2,sK1) )
        | ( ( ? [X4] :
                ( ~ r1_orders_2(sK0,sK1,X4)
                & r2_lattice3(sK0,X2,X4)
                & m1_subset_1(X4,u1_struct_0(sK0)) )
            | ~ r2_lattice3(sK0,X2,sK1) )
          & r1_yellow_0(sK0,X2)
          & k1_yellow_0(sK0,X2) = sK1 ) )
   => ( ( ( ~ r1_yellow_0(sK0,sK2)
          | sK1 != k1_yellow_0(sK0,sK2) )
        & ! [X3] :
            ( r1_orders_2(sK0,sK1,X3)
            | ~ r2_lattice3(sK0,sK2,X3)
            | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
        & r2_lattice3(sK0,sK2,sK1) )
      | ( ( ? [X4] :
              ( ~ r1_orders_2(sK0,sK1,X4)
              & r2_lattice3(sK0,sK2,X4)
              & m1_subset_1(X4,u1_struct_0(sK0)) )
          | ~ r2_lattice3(sK0,sK2,sK1) )
        & r1_yellow_0(sK0,sK2)
        & sK1 = k1_yellow_0(sK0,sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X4] :
        ( ~ r1_orders_2(sK0,sK1,X4)
        & r2_lattice3(sK0,sK2,X4)
        & m1_subset_1(X4,u1_struct_0(sK0)) )
   => ( ~ r1_orders_2(sK0,sK1,sK3)
      & r2_lattice3(sK0,sK2,sK3)
      & m1_subset_1(sK3,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( ~ r1_yellow_0(X0,X2)
                  | k1_yellow_0(X0,X2) != X1 )
                & ! [X3] :
                    ( r1_orders_2(X0,X1,X3)
                    | ~ r2_lattice3(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X2,X1) )
              | ( ( ? [X4] :
                      ( ~ r1_orders_2(X0,X1,X4)
                      & r2_lattice3(X0,X2,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r2_lattice3(X0,X2,X1) )
                & r1_yellow_0(X0,X2)
                & k1_yellow_0(X0,X2) = X1 ) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( ~ r1_yellow_0(X0,X2)
                  | k1_yellow_0(X0,X2) != X1 )
                & ! [X3] :
                    ( r1_orders_2(X0,X1,X3)
                    | ~ r2_lattice3(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X2,X1) )
              | ( ( ? [X4] :
                      ( ~ r1_orders_2(X0,X1,X4)
                      & r2_lattice3(X0,X2,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r2_lattice3(X0,X2,X1) )
                & r1_yellow_0(X0,X2)
                & k1_yellow_0(X0,X2) = X1 ) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( ( ( ! [X3] :
                        ( m1_subset_1(X3,u1_struct_0(X0))
                       => ( r2_lattice3(X0,X2,X3)
                         => r1_orders_2(X0,X1,X3) ) )
                    & r2_lattice3(X0,X2,X1) )
                 => ( r1_yellow_0(X0,X2)
                    & k1_yellow_0(X0,X2) = X1 ) )
                & ( ( r1_yellow_0(X0,X2)
                    & k1_yellow_0(X0,X2) = X1 )
                 => ( ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ( r2_lattice3(X0,X2,X4)
                         => r1_orders_2(X0,X1,X4) ) )
                    & r2_lattice3(X0,X2,X1) ) ) ) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( ( ( ! [X3] :
                        ( m1_subset_1(X3,u1_struct_0(X0))
                       => ( r2_lattice3(X0,X2,X3)
                         => r1_orders_2(X0,X1,X3) ) )
                    & r2_lattice3(X0,X2,X1) )
                 => ( r1_yellow_0(X0,X2)
                    & k1_yellow_0(X0,X2) = X1 ) )
                & ( ( r1_yellow_0(X0,X2)
                    & k1_yellow_0(X0,X2) = X1 )
                 => ( ! [X3] :
                        ( m1_subset_1(X3,u1_struct_0(X0))
                       => ( r2_lattice3(X0,X2,X3)
                         => r1_orders_2(X0,X1,X3) ) )
                    & r2_lattice3(X0,X2,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) )
               => ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 ) )
              & ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
               => ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_yellow_0)).

fof(f242,plain,(
    ! [X0] :
      ( ~ r2_lattice3(sK0,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_orders_2(sK0,sK1,X0)
      | ~ l1_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f241,f140])).

fof(f140,plain,(
    r1_yellow_0(sK0,sK2) ),
    inference(subsumption_resolution,[],[f139,f31])).

fof(f31,plain,
    ( r2_lattice3(sK0,sK2,sK1)
    | r1_yellow_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f139,plain,
    ( r1_yellow_0(sK0,sK2)
    | ~ r2_lattice3(sK0,sK2,sK1) ),
    inference(subsumption_resolution,[],[f138,f27])).

fof(f27,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f138,plain,
    ( r1_yellow_0(sK0,sK2)
    | ~ r2_lattice3(sK0,sK2,sK1)
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f137,f28])).

fof(f137,plain,
    ( r1_yellow_0(sK0,sK2)
    | ~ r2_lattice3(sK0,sK2,sK1)
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f136,f29])).

fof(f29,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f136,plain,
    ( r1_yellow_0(sK0,sK2)
    | ~ r2_lattice3(sK0,sK2,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(duplicate_literal_removal,[],[f135])).

fof(f135,plain,
    ( r1_yellow_0(sK0,sK2)
    | r1_yellow_0(sK0,sK2)
    | ~ r2_lattice3(sK0,sK2,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(resolution,[],[f134,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

% (13550)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
            | ! [X2] :
                ( ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
                  & r2_lattice3(X0,X1,sK5(X0,X1,X2))
                  & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ( ! [X5] :
                  ( r1_orders_2(X0,sK6(X0,X1),X5)
                  | ~ r2_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,sK6(X0,X1))
              & m1_subset_1(sK6(X0,X1),u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f23,f25,f24])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
        & r2_lattice3(X0,X1,sK5(X0,X1,X2))
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( ! [X5] :
              ( r1_orders_2(X0,X4,X5)
              | ~ r2_lattice3(X0,X1,X5)
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          & r2_lattice3(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ! [X5] :
            ( r1_orders_2(X0,sK6(X0,X1),X5)
            | ~ r2_lattice3(X0,X1,X5)
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        & r2_lattice3(X0,X1,sK6(X0,X1))
        & m1_subset_1(sK6(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
            | ! [X2] :
                ( ? [X3] :
                    ( ~ r1_orders_2(X0,X2,X3)
                    & r2_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X4] :
                ( ! [X5] :
                    ( r1_orders_2(X0,X4,X5)
                    | ~ r2_lattice3(X0,X1,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
            | ! [X2] :
                ( ? [X3] :
                    ( ~ r1_orders_2(X0,X2,X3)
                    & r2_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X2] :
                ( ! [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_lattice3(X0,X1,X3)
                   => r1_orders_2(X0,X2,X3) ) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_yellow_0)).

fof(f134,plain,
    ( ~ m1_subset_1(sK5(sK0,sK2,sK1),u1_struct_0(sK0))
    | r1_yellow_0(sK0,sK2) ),
    inference(subsumption_resolution,[],[f131,f31])).

fof(f131,plain,
    ( r1_yellow_0(sK0,sK2)
    | ~ r2_lattice3(sK0,sK2,sK1)
    | ~ m1_subset_1(sK5(sK0,sK2,sK1),u1_struct_0(sK0)) ),
    inference(duplicate_literal_removal,[],[f130])).

fof(f130,plain,
    ( r1_yellow_0(sK0,sK2)
    | ~ r2_lattice3(sK0,sK2,sK1)
    | ~ m1_subset_1(sK5(sK0,sK2,sK1),u1_struct_0(sK0))
    | r1_yellow_0(sK0,sK2)
    | r1_yellow_0(sK0,sK2) ),
    inference(resolution,[],[f105,f90])).

fof(f90,plain,
    ( r2_lattice3(sK0,sK2,sK5(sK0,sK2,sK1))
    | r1_yellow_0(sK0,sK2) ),
    inference(duplicate_literal_removal,[],[f89])).

fof(f89,plain,
    ( r2_lattice3(sK0,sK2,sK5(sK0,sK2,sK1))
    | r1_yellow_0(sK0,sK2)
    | r1_yellow_0(sK0,sK2) ),
    inference(resolution,[],[f79,f31])).

fof(f79,plain,(
    ! [X0] :
      ( ~ r2_lattice3(sK0,X0,sK1)
      | r2_lattice3(sK0,X0,sK5(sK0,X0,sK1))
      | r1_yellow_0(sK0,X0) ) ),
    inference(resolution,[],[f64,f29])).

fof(f64,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,X3,X4)
      | r2_lattice3(sK0,X3,sK5(sK0,X3,X4))
      | r1_yellow_0(sK0,X3) ) ),
    inference(subsumption_resolution,[],[f60,f28])).

fof(f60,plain,(
    ! [X4,X3] :
      ( r2_lattice3(sK0,X3,sK5(sK0,X3,X4))
      | ~ r2_lattice3(sK0,X3,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | r1_yellow_0(sK0,X3) ) ),
    inference(resolution,[],[f27,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | r2_lattice3(X0,X1,sK5(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f105,plain,(
    ! [X1] :
      ( ~ r2_lattice3(sK0,sK2,sK5(sK0,X1,sK1))
      | r1_yellow_0(sK0,X1)
      | ~ r2_lattice3(sK0,X1,sK1)
      | ~ m1_subset_1(sK5(sK0,X1,sK1),u1_struct_0(sK0))
      | r1_yellow_0(sK0,sK2) ) ),
    inference(resolution,[],[f95,f36])).

fof(f36,plain,(
    ! [X3] :
      ( r1_orders_2(sK0,sK1,X3)
      | ~ r2_lattice3(sK0,sK2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | r1_yellow_0(sK0,sK2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f95,plain,(
    ! [X0] :
      ( ~ r1_orders_2(sK0,sK1,sK5(sK0,X0,sK1))
      | ~ r2_lattice3(sK0,X0,sK1)
      | r1_yellow_0(sK0,X0) ) ),
    inference(resolution,[],[f65,f29])).

fof(f65,plain,(
    ! [X6,X5] :
      ( ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,X6,X5)
      | ~ r1_orders_2(sK0,X5,sK5(sK0,X6,X5))
      | r1_yellow_0(sK0,X6) ) ),
    inference(subsumption_resolution,[],[f61,f28])).

fof(f61,plain,(
    ! [X6,X5] :
      ( ~ r1_orders_2(sK0,X5,sK5(sK0,X6,X5))
      | ~ r2_lattice3(sK0,X6,X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | r1_yellow_0(sK0,X6) ) ),
    inference(resolution,[],[f27,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f241,plain,(
    ! [X0] :
      ( ~ r2_lattice3(sK0,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_yellow_0(sK0,sK2)
      | r1_orders_2(sK0,sK1,X0)
      | ~ l1_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f237,f29])).

fof(f237,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,sK2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_yellow_0(sK0,sK2)
      | r1_orders_2(sK0,sK1,X0)
      | ~ l1_orders_2(sK0) ) ),
    inference(superposition,[],[f56,f224])).

fof(f224,plain,(
    sK1 = k1_yellow_0(sK0,sK2) ),
    inference(subsumption_resolution,[],[f223,f30])).

fof(f30,plain,
    ( r2_lattice3(sK0,sK2,sK1)
    | sK1 = k1_yellow_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f223,plain,
    ( sK1 = k1_yellow_0(sK0,sK2)
    | ~ r2_lattice3(sK0,sK2,sK1) ),
    inference(subsumption_resolution,[],[f222,f28])).

fof(f222,plain,
    ( sK1 = k1_yellow_0(sK0,sK2)
    | ~ r2_lattice3(sK0,sK2,sK1)
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f221,f29])).

fof(f221,plain,
    ( sK1 = k1_yellow_0(sK0,sK2)
    | ~ r2_lattice3(sK0,sK2,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f220,f140])).

fof(f220,plain,
    ( sK1 = k1_yellow_0(sK0,sK2)
    | ~ r2_lattice3(sK0,sK2,sK1)
    | ~ r1_yellow_0(sK0,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(duplicate_literal_removal,[],[f219])).

fof(f219,plain,
    ( sK1 = k1_yellow_0(sK0,sK2)
    | sK1 = k1_yellow_0(sK0,sK2)
    | ~ r2_lattice3(sK0,sK2,sK1)
    | ~ r1_yellow_0(sK0,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f218,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | k1_yellow_0(X0,X1) = X2
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ( ~ r1_orders_2(X0,X2,sK4(X0,X1,X2))
                & r2_lattice3(X0,X1,sK4(X0,X1,X2))
                & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X2,X4)
                    | ~ r2_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f20])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK4(X0,X1,X2))
        & r2_lattice3(X0,X1,sK4(X0,X1,X2))
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X2,X4)
                    | ~ r2_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_yellow_0(X0,X1)
           => ( k1_yellow_0(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_lattice3(X0,X1,X3)
                     => r1_orders_2(X0,X2,X3) ) )
                & r2_lattice3(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_yellow_0)).

fof(f218,plain,
    ( ~ m1_subset_1(sK4(sK0,sK2,sK1),u1_struct_0(sK0))
    | sK1 = k1_yellow_0(sK0,sK2) ),
    inference(subsumption_resolution,[],[f217,f30])).

fof(f217,plain,
    ( ~ r2_lattice3(sK0,sK2,sK1)
    | sK1 = k1_yellow_0(sK0,sK2)
    | ~ m1_subset_1(sK4(sK0,sK2,sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f216,f140])).

fof(f216,plain,
    ( ~ r2_lattice3(sK0,sK2,sK1)
    | sK1 = k1_yellow_0(sK0,sK2)
    | ~ r1_yellow_0(sK0,sK2)
    | ~ m1_subset_1(sK4(sK0,sK2,sK1),u1_struct_0(sK0)) ),
    inference(duplicate_literal_removal,[],[f215])).

fof(f215,plain,
    ( ~ r2_lattice3(sK0,sK2,sK1)
    | sK1 = k1_yellow_0(sK0,sK2)
    | ~ r1_yellow_0(sK0,sK2)
    | ~ m1_subset_1(sK4(sK0,sK2,sK1),u1_struct_0(sK0))
    | sK1 = k1_yellow_0(sK0,sK2)
    | ~ r1_yellow_0(sK0,sK2)
    | sK1 = k1_yellow_0(sK0,sK2) ),
    inference(resolution,[],[f127,f117])).

fof(f117,plain,
    ( r2_lattice3(sK0,sK2,sK4(sK0,sK2,sK1))
    | ~ r1_yellow_0(sK0,sK2)
    | sK1 = k1_yellow_0(sK0,sK2) ),
    inference(duplicate_literal_removal,[],[f115])).

fof(f115,plain,
    ( ~ r1_yellow_0(sK0,sK2)
    | r2_lattice3(sK0,sK2,sK4(sK0,sK2,sK1))
    | sK1 = k1_yellow_0(sK0,sK2)
    | sK1 = k1_yellow_0(sK0,sK2) ),
    inference(resolution,[],[f106,f30])).

fof(f106,plain,(
    ! [X0] :
      ( ~ r2_lattice3(sK0,X0,sK1)
      | ~ r1_yellow_0(sK0,X0)
      | r2_lattice3(sK0,X0,sK4(sK0,X0,sK1))
      | sK1 = k1_yellow_0(sK0,X0) ) ),
    inference(resolution,[],[f66,f29])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,X0,X1)
      | ~ r1_yellow_0(sK0,X0)
      | r2_lattice3(sK0,X0,sK4(sK0,X0,X1))
      | k1_yellow_0(sK0,X0) = X1 ) ),
    inference(resolution,[],[f28,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | r2_lattice3(X0,X1,sK4(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_yellow_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f127,plain,(
    ! [X0] :
      ( ~ r2_lattice3(sK0,sK2,sK4(sK0,X0,sK1))
      | ~ r2_lattice3(sK0,X0,sK1)
      | sK1 = k1_yellow_0(sK0,X0)
      | ~ r1_yellow_0(sK0,X0)
      | ~ m1_subset_1(sK4(sK0,X0,sK1),u1_struct_0(sK0))
      | sK1 = k1_yellow_0(sK0,sK2) ) ),
    inference(resolution,[],[f118,f35])).

fof(f35,plain,(
    ! [X3] :
      ( r1_orders_2(sK0,sK1,X3)
      | ~ r2_lattice3(sK0,sK2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | sK1 = k1_yellow_0(sK0,sK2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f118,plain,(
    ! [X0] :
      ( ~ r1_orders_2(sK0,sK1,sK4(sK0,X0,sK1))
      | ~ r1_yellow_0(sK0,X0)
      | ~ r2_lattice3(sK0,X0,sK1)
      | sK1 = k1_yellow_0(sK0,X0) ) ),
    inference(resolution,[],[f67,f29])).

fof(f67,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_lattice3(sK0,X3,X2)
      | ~ r1_yellow_0(sK0,X3)
      | ~ r1_orders_2(sK0,X2,sK4(sK0,X3,X2))
      | k1_yellow_0(sK0,X3) = X2 ) ),
    inference(resolution,[],[f28,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,X2,sK4(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_yellow_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f56,plain,(
    ! [X4,X0,X1] :
      ( ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | r1_orders_2(X0,k1_yellow_0(X0,X1),X4)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k1_yellow_0(X0,X1) != X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f265,plain,(
    ~ r1_orders_2(sK0,sK1,sK3) ),
    inference(unit_resulting_resolution,[],[f240,f234])).

fof(f234,plain,
    ( ~ r1_orders_2(sK0,sK1,sK3)
    | ~ r2_lattice3(sK0,sK2,sK1) ),
    inference(subsumption_resolution,[],[f229,f140])).

fof(f229,plain,
    ( ~ r1_yellow_0(sK0,sK2)
    | ~ r1_orders_2(sK0,sK1,sK3)
    | ~ r2_lattice3(sK0,sK2,sK1) ),
    inference(trivial_inequality_removal,[],[f227])).

fof(f227,plain,
    ( sK1 != sK1
    | ~ r1_yellow_0(sK0,sK2)
    | ~ r1_orders_2(sK0,sK1,sK3)
    | ~ r2_lattice3(sK0,sK2,sK1) ),
    inference(backward_demodulation,[],[f44,f224])).

fof(f44,plain,
    ( sK1 != k1_yellow_0(sK0,sK2)
    | ~ r1_yellow_0(sK0,sK2)
    | ~ r1_orders_2(sK0,sK1,sK3)
    | ~ r2_lattice3(sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f240,plain,(
    r2_lattice3(sK0,sK2,sK1) ),
    inference(subsumption_resolution,[],[f239,f28])).

fof(f239,plain,
    ( r2_lattice3(sK0,sK2,sK1)
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f238,f140])).

fof(f238,plain,
    ( ~ r1_yellow_0(sK0,sK2)
    | r2_lattice3(sK0,sK2,sK1)
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f236,f29])).

fof(f236,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r1_yellow_0(sK0,sK2)
    | r2_lattice3(sK0,sK2,sK1)
    | ~ l1_orders_2(sK0) ),
    inference(superposition,[],[f57,f224])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | k1_yellow_0(X0,X1) != X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f244,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f240,f232])).

fof(f232,plain,
    ( ~ r2_lattice3(sK0,sK2,sK1)
    | m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f231,f140])).

fof(f231,plain,
    ( ~ r1_yellow_0(sK0,sK2)
    | m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK2,sK1) ),
    inference(trivial_inequality_removal,[],[f225])).

fof(f225,plain,
    ( sK1 != sK1
    | ~ r1_yellow_0(sK0,sK2)
    | m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK2,sK1) ),
    inference(backward_demodulation,[],[f42,f224])).

fof(f42,plain,
    ( sK1 != k1_yellow_0(sK0,sK2)
    | ~ r1_yellow_0(sK0,sK2)
    | m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f254,plain,(
    r2_lattice3(sK0,sK2,sK3) ),
    inference(unit_resulting_resolution,[],[f240,f233])).

fof(f233,plain,
    ( r2_lattice3(sK0,sK2,sK3)
    | ~ r2_lattice3(sK0,sK2,sK1) ),
    inference(subsumption_resolution,[],[f230,f140])).

fof(f230,plain,
    ( ~ r1_yellow_0(sK0,sK2)
    | r2_lattice3(sK0,sK2,sK3)
    | ~ r2_lattice3(sK0,sK2,sK1) ),
    inference(trivial_inequality_removal,[],[f226])).

fof(f226,plain,
    ( sK1 != sK1
    | ~ r1_yellow_0(sK0,sK2)
    | r2_lattice3(sK0,sK2,sK3)
    | ~ r2_lattice3(sK0,sK2,sK1) ),
    inference(backward_demodulation,[],[f43,f224])).

fof(f43,plain,
    ( sK1 != k1_yellow_0(sK0,sK2)
    | ~ r1_yellow_0(sK0,sK2)
    | r2_lattice3(sK0,sK2,sK3)
    | ~ r2_lattice3(sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f16])).

%------------------------------------------------------------------------------
