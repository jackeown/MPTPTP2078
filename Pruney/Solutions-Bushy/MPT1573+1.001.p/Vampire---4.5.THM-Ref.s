%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1573+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:08 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   74 (1476 expanded)
%              Number of leaves         :    6 ( 408 expanded)
%              Depth                    :   40
%              Number of atoms          :  402 (9031 expanded)
%              Number of equality atoms :   90 (1515 expanded)
%              Maximal formula depth    :   11 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (8225)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
fof(f308,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f307])).

fof(f307,plain,(
    k1_yellow_0(sK0,sK1) != k1_yellow_0(sK0,sK1) ),
    inference(superposition,[],[f22,f272])).

fof(f272,plain,(
    k1_yellow_0(sK0,sK1) = k1_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0))) ),
    inference(resolution,[],[f271,f19])).

fof(f19,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( k1_yellow_0(sK0,sK1) != k1_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
    & ( r1_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
      | r1_yellow_0(sK0,sK1) )
    & l1_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f13,f12])).

fof(f12,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_yellow_0(X0,X1) != k1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
            & ( r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
              | r1_yellow_0(X0,X1) ) )
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k1_yellow_0(sK0,X1) != k1_yellow_0(sK0,k3_xboole_0(X1,u1_struct_0(sK0)))
          & ( r1_yellow_0(sK0,k3_xboole_0(X1,u1_struct_0(sK0)))
            | r1_yellow_0(sK0,X1) ) )
      & l1_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X1] :
        ( k1_yellow_0(sK0,X1) != k1_yellow_0(sK0,k3_xboole_0(X1,u1_struct_0(sK0)))
        & ( r1_yellow_0(sK0,k3_xboole_0(X1,u1_struct_0(sK0)))
          | r1_yellow_0(sK0,X1) ) )
   => ( k1_yellow_0(sK0,sK1) != k1_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
      & ( r1_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
        | r1_yellow_0(sK0,sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_yellow_0(X0,X1) != k1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
          & ( r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
            | r1_yellow_0(X0,X1) ) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_yellow_0(X0,X1) != k1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
          & ( r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
            | r1_yellow_0(X0,X1) ) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
              | r1_yellow_0(X0,X1) )
           => k1_yellow_0(X0,X1) = k1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
            | r1_yellow_0(X0,X1) )
         => k1_yellow_0(X0,X1) = k1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_yellow_0)).

fof(f271,plain,
    ( v2_struct_0(sK0)
    | k1_yellow_0(sK0,sK1) = k1_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0))) ),
    inference(duplicate_literal_removal,[],[f268])).

fof(f268,plain,
    ( k1_yellow_0(sK0,sK1) = k1_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | k1_yellow_0(sK0,sK1) = k1_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f262,f193])).

fof(f193,plain,
    ( ~ r2_lattice3(sK0,sK1,sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0))))
    | k1_yellow_0(sK0,sK1) = k1_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f192,f20])).

fof(f20,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f192,plain,
    ( ~ l1_orders_2(sK0)
    | ~ r2_lattice3(sK0,sK1,sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0))))
    | k1_yellow_0(sK0,sK1) = k1_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f191])).

fof(f191,plain,
    ( v2_struct_0(sK0)
    | ~ r2_lattice3(sK0,sK1,sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0))))
    | k1_yellow_0(sK0,sK1) = k1_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | k1_yellow_0(sK0,sK1) = k1_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f188,f93])).

fof(f93,plain,
    ( r1_yellow_0(sK0,sK1)
    | k1_yellow_0(sK0,sK1) = k1_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f90])).

fof(f90,plain,
    ( v2_struct_0(sK0)
    | k1_yellow_0(sK0,sK1) = k1_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
    | r1_yellow_0(sK0,sK1)
    | k1_yellow_0(sK0,sK1) = k1_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | r1_yellow_0(sK0,sK1) ),
    inference(resolution,[],[f89,f74])).

fof(f74,plain,
    ( r2_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1))
    | k1_yellow_0(sK0,sK1) = k1_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | r1_yellow_0(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f71])).

fof(f71,plain,
    ( r1_yellow_0(sK0,sK1)
    | k1_yellow_0(sK0,sK1) = k1_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | r1_yellow_0(sK0,sK1)
    | v2_struct_0(sK0)
    | r2_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1))
    | k1_yellow_0(sK0,sK1) = k1_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0))) ),
    inference(resolution,[],[f66,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r2_lattice3(sK0,X0,sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),X1))
      | r1_yellow_0(sK0,sK1)
      | v2_struct_0(sK0)
      | r2_lattice3(sK0,k3_xboole_0(X0,u1_struct_0(sK0)),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),X1))
      | k1_yellow_0(sK0,X1) = k1_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f37,f20])).

fof(f37,plain,(
    ! [X6,X7] :
      ( ~ l1_orders_2(sK0)
      | v2_struct_0(sK0)
      | r1_yellow_0(sK0,sK1)
      | ~ r2_lattice3(sK0,X7,sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),X6))
      | r2_lattice3(sK0,k3_xboole_0(X7,u1_struct_0(sK0)),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),X6))
      | k1_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0))) = k1_yellow_0(sK0,X6) ) ),
    inference(duplicate_literal_removal,[],[f36])).

fof(f36,plain,(
    ! [X6,X7] :
      ( k1_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0))) = k1_yellow_0(sK0,X6)
      | v2_struct_0(sK0)
      | r1_yellow_0(sK0,sK1)
      | ~ r2_lattice3(sK0,X7,sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),X6))
      | r2_lattice3(sK0,k3_xboole_0(X7,u1_struct_0(sK0)),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),X6))
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f32,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ~ r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2) )
            & ( r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
              | ~ r1_lattice3(X0,X1,X2) )
            & ( r2_lattice3(X0,X1,X2)
              | ~ r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2) )
            & ( r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ~ r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2) )
            & ( r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
              | ~ r1_lattice3(X0,X1,X2) )
            & ( r2_lattice3(X0,X1,X2)
              | ~ r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2) )
            & ( r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( ( r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
             => r1_lattice3(X0,X1,X2) )
            & ( r1_lattice3(X0,X1,X2)
             => r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2) )
            & ( r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
             => r2_lattice3(X0,X1,X2) )
            & ( r2_lattice3(X0,X1,X2)
             => r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_yellow_0)).

fof(f32,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),X0),u1_struct_0(sK0))
      | k1_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0))) = k1_yellow_0(sK0,X0)
      | v2_struct_0(sK0)
      | r1_yellow_0(sK0,sK1) ) ),
    inference(resolution,[],[f31,f21])).

fof(f21,plain,
    ( r1_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
    | r1_yellow_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_yellow_0(sK0,X0)
      | m1_subset_1(sK2(sK0,X0,X1),u1_struct_0(sK0))
      | k1_yellow_0(sK0,X1) = k1_yellow_0(sK0,X0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f27,f20])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2)
          | ( ( ~ r2_lattice3(X0,X2,sK2(X0,X1,X2))
              | ~ r2_lattice3(X0,X1,sK2(X0,X1,X2)) )
            & ( r2_lattice3(X0,X2,sK2(X0,X1,X2))
              | r2_lattice3(X0,X1,sK2(X0,X1,X2)) )
            & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) )
          | ~ r1_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f17])).

fof(f17,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_lattice3(X0,X2,X3)
            | ~ r2_lattice3(X0,X1,X3) )
          & ( r2_lattice3(X0,X2,X3)
            | r2_lattice3(X0,X1,X3) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ( ~ r2_lattice3(X0,X2,sK2(X0,X1,X2))
          | ~ r2_lattice3(X0,X1,sK2(X0,X1,X2)) )
        & ( r2_lattice3(X0,X2,sK2(X0,X1,X2))
          | r2_lattice3(X0,X1,sK2(X0,X1,X2)) )
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2)
          | ? [X3] :
              ( ( ~ r2_lattice3(X0,X2,X3)
                | ~ r2_lattice3(X0,X1,X3) )
              & ( r2_lattice3(X0,X2,X3)
                | r2_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r1_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2)
          | ? [X3] :
              ( ( ~ r2_lattice3(X0,X2,X3)
                | ~ r2_lattice3(X0,X1,X3) )
              & ( r2_lattice3(X0,X2,X3)
                | r2_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r1_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2)
          | ? [X3] :
              ( ( r2_lattice3(X0,X1,X3)
              <~> r2_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r1_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2)
          | ? [X3] :
              ( ( r2_lattice3(X0,X1,X3)
              <~> r2_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r1_yellow_0(X0,X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_yellow_0)).

fof(f66,plain,
    ( r2_lattice3(sK0,sK1,sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1))
    | r1_yellow_0(sK0,sK1)
    | k1_yellow_0(sK0,sK1) = k1_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(factoring,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( r2_lattice3(sK0,sK1,sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),X0))
      | r2_lattice3(sK0,X0,sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),X0))
      | r1_yellow_0(sK0,sK1)
      | k1_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0))) = k1_yellow_0(sK0,X0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( r1_yellow_0(sK0,sK1)
      | v2_struct_0(sK0)
      | r2_lattice3(sK0,sK1,sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),X0))
      | k1_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0))) = k1_yellow_0(sK0,X0)
      | r2_lattice3(sK0,X0,sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),X0))
      | k1_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0))) = k1_yellow_0(sK0,X0)
      | v2_struct_0(sK0)
      | r1_yellow_0(sK0,sK1) ) ),
    inference(resolution,[],[f53,f42])).

fof(f42,plain,(
    ! [X0] :
      ( r2_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),X0))
      | r2_lattice3(sK0,X0,sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),X0))
      | k1_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0))) = k1_yellow_0(sK0,X0)
      | v2_struct_0(sK0)
      | r1_yellow_0(sK0,sK1) ) ),
    inference(resolution,[],[f41,f21])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_yellow_0(sK0,X1)
      | r2_lattice3(sK0,X1,sK2(sK0,X1,X0))
      | r2_lattice3(sK0,X0,sK2(sK0,X1,X0))
      | k1_yellow_0(sK0,X1) = k1_yellow_0(sK0,X0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f28,f20])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | r2_lattice3(X0,X2,sK2(X0,X1,X2))
      | r2_lattice3(X0,X1,sK2(X0,X1,X2))
      | ~ r1_yellow_0(X0,X1)
      | k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r2_lattice3(sK0,k3_xboole_0(X0,u1_struct_0(sK0)),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),X1))
      | r1_yellow_0(sK0,sK1)
      | v2_struct_0(sK0)
      | r2_lattice3(sK0,X0,sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),X1))
      | k1_yellow_0(sK0,X1) = k1_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f38,f20])).

fof(f38,plain,(
    ! [X4,X5] :
      ( ~ l1_orders_2(sK0)
      | v2_struct_0(sK0)
      | r1_yellow_0(sK0,sK1)
      | ~ r2_lattice3(sK0,k3_xboole_0(X5,u1_struct_0(sK0)),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),X4))
      | r2_lattice3(sK0,X5,sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),X4))
      | k1_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0))) = k1_yellow_0(sK0,X4) ) ),
    inference(duplicate_literal_removal,[],[f35])).

fof(f35,plain,(
    ! [X4,X5] :
      ( k1_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0))) = k1_yellow_0(sK0,X4)
      | v2_struct_0(sK0)
      | r1_yellow_0(sK0,sK1)
      | ~ r2_lattice3(sK0,k3_xboole_0(X5,u1_struct_0(sK0)),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),X4))
      | r2_lattice3(sK0,X5,sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),X4))
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f32,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
      | r2_lattice3(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f89,plain,
    ( ~ r2_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1))
    | v2_struct_0(sK0)
    | k1_yellow_0(sK0,sK1) = k1_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
    | r1_yellow_0(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f88])).

fof(f88,plain,
    ( v2_struct_0(sK0)
    | ~ r2_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1))
    | k1_yellow_0(sK0,sK1) = k1_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
    | r1_yellow_0(sK0,sK1)
    | r1_yellow_0(sK0,sK1) ),
    inference(resolution,[],[f87,f21])).

fof(f87,plain,
    ( ~ r1_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ r2_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1))
    | k1_yellow_0(sK0,sK1) = k1_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
    | r1_yellow_0(sK0,sK1) ),
    inference(resolution,[],[f73,f20])).

fof(f73,plain,
    ( ~ l1_orders_2(sK0)
    | k1_yellow_0(sK0,sK1) = k1_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ r2_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1))
    | ~ r1_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
    | r1_yellow_0(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f72])).

fof(f72,plain,
    ( r1_yellow_0(sK0,sK1)
    | k1_yellow_0(sK0,sK1) = k1_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | k1_yellow_0(sK0,sK1) = k1_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
    | ~ r2_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK1))
    | ~ r1_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f66,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_lattice3(X0,X2,sK2(X0,X1,X2))
      | k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2)
      | ~ r2_lattice3(X0,X1,sK2(X0,X1,X2))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f188,plain,
    ( ~ r1_yellow_0(sK0,sK1)
    | v2_struct_0(sK0)
    | ~ r2_lattice3(sK0,sK1,sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0))))
    | k1_yellow_0(sK0,sK1) = k1_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0) ),
    inference(duplicate_literal_removal,[],[f187])).

fof(f187,plain,
    ( k1_yellow_0(sK0,sK1) = k1_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | k1_yellow_0(sK0,sK1) = k1_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
    | ~ r2_lattice3(sK0,sK1,sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0))))
    | ~ r1_yellow_0(sK0,sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f181,f29])).

fof(f181,plain,
    ( r2_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0))))
    | k1_yellow_0(sK0,sK1) = k1_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f180])).

fof(f180,plain,
    ( r2_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0))))
    | k1_yellow_0(sK0,sK1) = k1_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | k1_yellow_0(sK0,sK1) = k1_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0))) ),
    inference(factoring,[],[f152])).

fof(f152,plain,(
    ! [X0] :
      ( r2_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2(sK0,sK1,X0))
      | r2_lattice3(sK0,X0,sK2(sK0,sK1,X0))
      | k1_yellow_0(sK0,sK1) = k1_yellow_0(sK0,X0)
      | v2_struct_0(sK0)
      | k1_yellow_0(sK0,sK1) = k1_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0))) ) ),
    inference(duplicate_literal_removal,[],[f149])).

fof(f149,plain,(
    ! [X0] :
      ( k1_yellow_0(sK0,sK1) = k1_yellow_0(sK0,X0)
      | k1_yellow_0(sK0,sK1) = k1_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
      | r2_lattice3(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)),sK2(sK0,sK1,X0))
      | v2_struct_0(sK0)
      | r2_lattice3(sK0,X0,sK2(sK0,sK1,X0))
      | k1_yellow_0(sK0,sK1) = k1_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
      | v2_struct_0(sK0)
      | k1_yellow_0(sK0,sK1) = k1_yellow_0(sK0,X0) ) ),
    inference(resolution,[],[f148,f97])).

fof(f97,plain,(
    ! [X0] :
      ( r2_lattice3(sK0,sK1,sK2(sK0,sK1,X0))
      | r2_lattice3(sK0,X0,sK2(sK0,sK1,X0))
      | k1_yellow_0(sK0,sK1) = k1_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
      | v2_struct_0(sK0)
      | k1_yellow_0(sK0,sK1) = k1_yellow_0(sK0,X0) ) ),
    inference(duplicate_literal_removal,[],[f94])).

fof(f94,plain,(
    ! [X0] :
      ( k1_yellow_0(sK0,sK1) = k1_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
      | v2_struct_0(sK0)
      | r2_lattice3(sK0,sK1,sK2(sK0,sK1,X0))
      | r2_lattice3(sK0,X0,sK2(sK0,sK1,X0))
      | k1_yellow_0(sK0,sK1) = k1_yellow_0(sK0,X0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f93,f41])).

fof(f148,plain,(
    ! [X0,X1] :
      ( ~ r2_lattice3(sK0,X1,sK2(sK0,sK1,X0))
      | k1_yellow_0(sK0,sK1) = k1_yellow_0(sK0,X0)
      | k1_yellow_0(sK0,sK1) = k1_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
      | r2_lattice3(sK0,k3_xboole_0(X1,u1_struct_0(sK0)),sK2(sK0,sK1,X0))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f102,f20])).

fof(f102,plain,(
    ! [X6,X7] :
      ( ~ l1_orders_2(sK0)
      | k1_yellow_0(sK0,sK1) = k1_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
      | k1_yellow_0(sK0,sK1) = k1_yellow_0(sK0,X6)
      | ~ r2_lattice3(sK0,X7,sK2(sK0,sK1,X6))
      | r2_lattice3(sK0,k3_xboole_0(X7,u1_struct_0(sK0)),sK2(sK0,sK1,X6))
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f101])).

fof(f101,plain,(
    ! [X6,X7] :
      ( v2_struct_0(sK0)
      | k1_yellow_0(sK0,sK1) = k1_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
      | k1_yellow_0(sK0,sK1) = k1_yellow_0(sK0,X6)
      | ~ r2_lattice3(sK0,X7,sK2(sK0,sK1,X6))
      | r2_lattice3(sK0,k3_xboole_0(X7,u1_struct_0(sK0)),sK2(sK0,sK1,X6))
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f96,f23])).

fof(f96,plain,(
    ! [X1] :
      ( m1_subset_1(sK2(sK0,sK1,X1),u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | k1_yellow_0(sK0,sK1) = k1_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
      | k1_yellow_0(sK0,X1) = k1_yellow_0(sK0,sK1) ) ),
    inference(duplicate_literal_removal,[],[f95])).

fof(f95,plain,(
    ! [X1] :
      ( k1_yellow_0(sK0,sK1) = k1_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
      | v2_struct_0(sK0)
      | m1_subset_1(sK2(sK0,sK1,X1),u1_struct_0(sK0))
      | k1_yellow_0(sK0,X1) = k1_yellow_0(sK0,sK1)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f93,f31])).

fof(f262,plain,
    ( r2_lattice3(sK0,sK1,sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0))))
    | k1_yellow_0(sK0,sK1) = k1_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f259])).

fof(f259,plain,
    ( k1_yellow_0(sK0,sK1) = k1_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
    | k1_yellow_0(sK0,sK1) = k1_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
    | r2_lattice3(sK0,sK1,sK2(sK0,sK1,k3_xboole_0(sK1,u1_struct_0(sK0))))
    | v2_struct_0(sK0)
    | k1_yellow_0(sK0,sK1) = k1_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f253,f181])).

fof(f253,plain,(
    ! [X0,X1] :
      ( ~ r2_lattice3(sK0,k3_xboole_0(X1,u1_struct_0(sK0)),sK2(sK0,sK1,X0))
      | k1_yellow_0(sK0,sK1) = k1_yellow_0(sK0,X0)
      | k1_yellow_0(sK0,sK1) = k1_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
      | r2_lattice3(sK0,X1,sK2(sK0,sK1,X0))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f103,f20])).

fof(f103,plain,(
    ! [X4,X5] :
      ( ~ l1_orders_2(sK0)
      | k1_yellow_0(sK0,sK1) = k1_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
      | k1_yellow_0(sK0,sK1) = k1_yellow_0(sK0,X4)
      | ~ r2_lattice3(sK0,k3_xboole_0(X5,u1_struct_0(sK0)),sK2(sK0,sK1,X4))
      | r2_lattice3(sK0,X5,sK2(sK0,sK1,X4))
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f100])).

fof(f100,plain,(
    ! [X4,X5] :
      ( v2_struct_0(sK0)
      | k1_yellow_0(sK0,sK1) = k1_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0)))
      | k1_yellow_0(sK0,sK1) = k1_yellow_0(sK0,X4)
      | ~ r2_lattice3(sK0,k3_xboole_0(X5,u1_struct_0(sK0)),sK2(sK0,sK1,X4))
      | r2_lattice3(sK0,X5,sK2(sK0,sK1,X4))
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f96,f24])).

fof(f22,plain,(
    k1_yellow_0(sK0,sK1) != k1_yellow_0(sK0,k3_xboole_0(sK1,u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f14])).

%------------------------------------------------------------------------------
