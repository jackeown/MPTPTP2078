%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1569+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:07 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   69 (1237 expanded)
%              Number of leaves         :    8 ( 351 expanded)
%              Depth                    :   25
%              Number of atoms          :  362 (9879 expanded)
%              Number of equality atoms :   27 (1072 expanded)
%              Maximal formula depth    :   13 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f151,plain,(
    $false ),
    inference(subsumption_resolution,[],[f150,f105])).

fof(f105,plain,(
    ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK1),sK3(sK0,sK2,k1_yellow_0(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f27,f56,f43,f31,f98,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_yellow_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ( ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
                & r2_lattice3(X0,X1,sK3(X0,X1,X2))
                & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f20])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
        & r2_lattice3(X0,X1,sK3(X0,X1,X2))
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_yellow_0)).

fof(f98,plain,(
    r1_yellow_0(sK0,sK2) ),
    inference(subsumption_resolution,[],[f97,f26])).

fof(f26,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( k1_yellow_0(sK0,sK1) != k1_yellow_0(sK0,sK2)
    & ! [X3] :
        ( ( ( r2_lattice3(sK0,sK1,X3)
            | ~ r2_lattice3(sK0,sK2,X3) )
          & ( r2_lattice3(sK0,sK2,X3)
            | ~ r2_lattice3(sK0,sK1,X3) ) )
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    & r1_yellow_0(sK0,sK1)
    & l1_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f15,f14])).

fof(f14,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k1_yellow_0(X0,X1) != k1_yellow_0(X0,X2)
            & ! [X3] :
                ( ( ( r2_lattice3(X0,X1,X3)
                    | ~ r2_lattice3(X0,X2,X3) )
                  & ( r2_lattice3(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3) ) )
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & r1_yellow_0(X0,X1) )
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X2,X1] :
          ( k1_yellow_0(sK0,X1) != k1_yellow_0(sK0,X2)
          & ! [X3] :
              ( ( ( r2_lattice3(sK0,X1,X3)
                  | ~ r2_lattice3(sK0,X2,X3) )
                & ( r2_lattice3(sK0,X2,X3)
                  | ~ r2_lattice3(sK0,X1,X3) ) )
              | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
          & r1_yellow_0(sK0,X1) )
      & l1_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X2,X1] :
        ( k1_yellow_0(sK0,X1) != k1_yellow_0(sK0,X2)
        & ! [X3] :
            ( ( ( r2_lattice3(sK0,X1,X3)
                | ~ r2_lattice3(sK0,X2,X3) )
              & ( r2_lattice3(sK0,X2,X3)
                | ~ r2_lattice3(sK0,X1,X3) ) )
            | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
        & r1_yellow_0(sK0,X1) )
   => ( k1_yellow_0(sK0,sK1) != k1_yellow_0(sK0,sK2)
      & ! [X3] :
          ( ( ( r2_lattice3(sK0,sK1,X3)
              | ~ r2_lattice3(sK0,sK2,X3) )
            & ( r2_lattice3(sK0,sK2,X3)
              | ~ r2_lattice3(sK0,sK1,X3) ) )
          | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
      & r1_yellow_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k1_yellow_0(X0,X1) != k1_yellow_0(X0,X2)
          & ! [X3] :
              ( ( ( r2_lattice3(X0,X1,X3)
                  | ~ r2_lattice3(X0,X2,X3) )
                & ( r2_lattice3(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3) ) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & r1_yellow_0(X0,X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k1_yellow_0(X0,X1) != k1_yellow_0(X0,X2)
          & ! [X3] :
              ( ( r2_lattice3(X0,X1,X3)
              <=> r2_lattice3(X0,X2,X3) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & r1_yellow_0(X0,X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k1_yellow_0(X0,X1) != k1_yellow_0(X0,X2)
          & ! [X3] :
              ( ( r2_lattice3(X0,X1,X3)
              <=> r2_lattice3(X0,X2,X3) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & r1_yellow_0(X0,X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1,X2] :
            ( ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_lattice3(X0,X1,X3)
                  <=> r2_lattice3(X0,X2,X3) ) )
              & r1_yellow_0(X0,X1) )
           => k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( ( ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_lattice3(X0,X1,X3)
                <=> r2_lattice3(X0,X2,X3) ) )
            & r1_yellow_0(X0,X1) )
         => k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_yellow_0)).

fof(f97,plain,
    ( r1_yellow_0(sK0,sK2)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f96,f27])).

fof(f96,plain,
    ( r1_yellow_0(sK0,sK2)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f95,f28])).

fof(f28,plain,(
    r1_yellow_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f95,plain,
    ( r1_yellow_0(sK0,sK2)
    | ~ r1_yellow_0(sK0,sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f94])).

fof(f94,plain,
    ( r1_yellow_0(sK0,sK2)
    | ~ r1_yellow_0(sK0,sK1)
    | r1_yellow_0(sK0,sK2)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f86,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | r1_yellow_0(X0,X2)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ( ( ~ r2_lattice3(X0,X2,sK4(X0,X1,X2))
              | ~ r2_lattice3(X0,X1,sK4(X0,X1,X2)) )
            & ( r2_lattice3(X0,X2,sK4(X0,X1,X2))
              | r2_lattice3(X0,X1,sK4(X0,X1,X2)) )
            & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f24])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_lattice3(X0,X2,X3)
            | ~ r2_lattice3(X0,X1,X3) )
          & ( r2_lattice3(X0,X2,X3)
            | r2_lattice3(X0,X1,X3) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ( ~ r2_lattice3(X0,X2,sK4(X0,X1,X2))
          | ~ r2_lattice3(X0,X1,sK4(X0,X1,X2)) )
        & ( r2_lattice3(X0,X2,sK4(X0,X1,X2))
          | r2_lattice3(X0,X1,sK4(X0,X1,X2)) )
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ? [X3] :
              ( ( ~ r2_lattice3(X0,X2,X3)
                | ~ r2_lattice3(X0,X1,X3) )
              & ( r2_lattice3(X0,X2,X3)
                | r2_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ? [X3] :
              ( ( ~ r2_lattice3(X0,X2,X3)
                | ~ r2_lattice3(X0,X1,X3) )
              & ( r2_lattice3(X0,X2,X3)
                | r2_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ? [X3] :
              ( ( r2_lattice3(X0,X1,X3)
              <~> r2_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ? [X3] :
              ( ( r2_lattice3(X0,X1,X3)
              <~> r2_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( ( r1_yellow_0(X0,X1)
            & ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_lattice3(X0,X1,X3)
                <=> r2_lattice3(X0,X2,X3) ) ) )
         => r1_yellow_0(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_yellow_0)).

fof(f86,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1,sK2),u1_struct_0(sK0))
    | r1_yellow_0(sK0,sK2) ),
    inference(subsumption_resolution,[],[f85,f75])).

fof(f75,plain,
    ( r2_lattice3(sK0,sK1,sK4(sK0,sK1,sK2))
    | r1_yellow_0(sK0,sK2)
    | ~ m1_subset_1(sK4(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    inference(duplicate_literal_removal,[],[f73])).

fof(f73,plain,
    ( r2_lattice3(sK0,sK1,sK4(sK0,sK1,sK2))
    | r1_yellow_0(sK0,sK2)
    | r2_lattice3(sK0,sK1,sK4(sK0,sK1,sK2))
    | ~ m1_subset_1(sK4(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    inference(resolution,[],[f72,f30])).

fof(f30,plain,(
    ! [X3] :
      ( ~ r2_lattice3(sK0,sK2,X3)
      | r2_lattice3(sK0,sK1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f72,plain,(
    ! [X0] :
      ( r2_lattice3(sK0,sK1,sK4(sK0,sK1,X0))
      | r2_lattice3(sK0,X0,sK4(sK0,sK1,X0))
      | r1_yellow_0(sK0,X0) ) ),
    inference(resolution,[],[f48,f28])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_yellow_0(sK0,X0)
      | r2_lattice3(sK0,X1,sK4(sK0,X0,X1))
      | r2_lattice3(sK0,X0,sK4(sK0,X0,X1))
      | r1_yellow_0(sK0,X1) ) ),
    inference(subsumption_resolution,[],[f44,f26])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_yellow_0(sK0,X0)
      | r2_lattice3(sK0,X1,sK4(sK0,X0,X1))
      | r2_lattice3(sK0,X0,sK4(sK0,X0,X1))
      | r1_yellow_0(sK0,X1)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f27,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,X1)
      | r2_lattice3(X0,X2,sK4(X0,X1,X2))
      | r2_lattice3(X0,X1,sK4(X0,X1,X2))
      | r1_yellow_0(X0,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f85,plain,
    ( r1_yellow_0(sK0,sK2)
    | ~ m1_subset_1(sK4(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK1,sK4(sK0,sK1,sK2)) ),
    inference(duplicate_literal_removal,[],[f82])).

fof(f82,plain,
    ( r1_yellow_0(sK0,sK2)
    | ~ m1_subset_1(sK4(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK1,sK4(sK0,sK1,sK2))
    | ~ m1_subset_1(sK4(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    inference(resolution,[],[f80,f29])).

fof(f29,plain,(
    ! [X3] :
      ( r2_lattice3(sK0,sK2,X3)
      | ~ r2_lattice3(sK0,sK1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f80,plain,
    ( ~ r2_lattice3(sK0,sK2,sK4(sK0,sK1,sK2))
    | r1_yellow_0(sK0,sK2)
    | ~ m1_subset_1(sK4(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    inference(duplicate_literal_removal,[],[f78])).

fof(f78,plain,
    ( ~ r2_lattice3(sK0,sK2,sK4(sK0,sK1,sK2))
    | r1_yellow_0(sK0,sK2)
    | r1_yellow_0(sK0,sK2)
    | ~ m1_subset_1(sK4(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    inference(resolution,[],[f76,f75])).

fof(f76,plain,(
    ! [X0] :
      ( ~ r2_lattice3(sK0,sK1,sK4(sK0,sK1,X0))
      | ~ r2_lattice3(sK0,X0,sK4(sK0,sK1,X0))
      | r1_yellow_0(sK0,X0) ) ),
    inference(resolution,[],[f49,f28])).

fof(f49,plain,(
    ! [X2,X3] :
      ( ~ r1_yellow_0(sK0,X2)
      | ~ r2_lattice3(sK0,X3,sK4(sK0,X2,X3))
      | ~ r2_lattice3(sK0,X2,sK4(sK0,X2,X3))
      | r1_yellow_0(sK0,X3) ) ),
    inference(subsumption_resolution,[],[f45,f26])).

fof(f45,plain,(
    ! [X2,X3] :
      ( ~ r1_yellow_0(sK0,X2)
      | ~ r2_lattice3(sK0,X3,sK4(sK0,X2,X3))
      | ~ r2_lattice3(sK0,X2,sK4(sK0,X2,X3))
      | r1_yellow_0(sK0,X3)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f27,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X2,sK4(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,sK4(X0,X1,X2))
      | r1_yellow_0(X0,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f31,plain,(
    k1_yellow_0(sK0,sK1) != k1_yellow_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f43,plain,(
    ! [X0] : m1_subset_1(k1_yellow_0(sK0,X0),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f27,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).

fof(f56,plain,(
    r2_lattice3(sK0,sK2,k1_yellow_0(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f43,f50,f29])).

fof(f50,plain,(
    r2_lattice3(sK0,sK1,k1_yellow_0(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f27,f28,f43,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | k1_yellow_0(X0,X1) != X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f27,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f150,plain,(
    r1_orders_2(sK0,k1_yellow_0(sK0,sK1),sK3(sK0,sK2,k1_yellow_0(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f27,f28,f43,f103,f144,f41])).

fof(f41,plain,(
    ! [X4,X0,X1] :
      ( ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | r1_orders_2(X0,k1_yellow_0(X0,X1),X4)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k1_yellow_0(X0,X1) != X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f144,plain,(
    r2_lattice3(sK0,sK1,sK3(sK0,sK2,k1_yellow_0(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f103,f104,f30])).

fof(f104,plain,(
    r2_lattice3(sK0,sK2,sK3(sK0,sK2,k1_yellow_0(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f27,f56,f43,f31,f98,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | r2_lattice3(X0,X1,sK3(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_yellow_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f103,plain,(
    m1_subset_1(sK3(sK0,sK2,k1_yellow_0(sK0,sK1)),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f27,f43,f56,f31,f98,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | k1_yellow_0(X0,X1) = X2
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

%------------------------------------------------------------------------------
