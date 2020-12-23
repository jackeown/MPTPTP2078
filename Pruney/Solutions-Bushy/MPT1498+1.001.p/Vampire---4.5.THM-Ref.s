%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1498+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:58 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 503 expanded)
%              Number of leaves         :    7 ( 141 expanded)
%              Depth                    :   15
%              Number of atoms          :  228 (3547 expanded)
%              Number of equality atoms :   11 (  37 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f66,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f23,f24,f25,f42,f60])).

fof(f60,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l3_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f55,f59])).

fof(f59,plain,
    ( r4_lattice3(sK1,sK2,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l3_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1) ),
    inference(duplicate_literal_removal,[],[f56])).

fof(f56,plain,
    ( r4_lattice3(sK1,sK2,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l3_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | r4_lattice3(sK1,sK2,sK0) ),
    inference(resolution,[],[f50,f39])).

fof(f39,plain,
    ( r2_lattice3(k3_lattice3(sK1),sK0,sK2)
    | r4_lattice3(sK1,sK2,sK0) ),
    inference(superposition,[],[f27,f34])).

fof(f34,plain,(
    sK2 = k5_lattice3(sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f23,f24,f25,f26,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
      | k5_lattice3(X0,X1) = X1
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_lattice3(X0,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0))) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_lattice3(X0,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0))) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
         => k5_lattice3(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_lattice3)).

fof(f26,plain,(
    m1_subset_1(sK2,u1_struct_0(k3_lattice3(sK1))) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ( ~ r4_lattice3(sK1,k5_lattice3(sK1,sK2),sK0)
      | ~ r2_lattice3(k3_lattice3(sK1),sK0,sK2) )
    & ( r4_lattice3(sK1,k5_lattice3(sK1,sK2),sK0)
      | r2_lattice3(k3_lattice3(sK1),sK0,sK2) )
    & m1_subset_1(sK2,u1_struct_0(k3_lattice3(sK1)))
    & l3_lattices(sK1)
    & v10_lattices(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f20,f19])).

fof(f19,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r4_lattice3(X1,k5_lattice3(X1,X2),X0)
              | ~ r2_lattice3(k3_lattice3(X1),X0,X2) )
            & ( r4_lattice3(X1,k5_lattice3(X1,X2),X0)
              | r2_lattice3(k3_lattice3(X1),X0,X2) )
            & m1_subset_1(X2,u1_struct_0(k3_lattice3(X1))) )
        & l3_lattices(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ( ~ r4_lattice3(sK1,k5_lattice3(sK1,X2),sK0)
            | ~ r2_lattice3(k3_lattice3(sK1),sK0,X2) )
          & ( r4_lattice3(sK1,k5_lattice3(sK1,X2),sK0)
            | r2_lattice3(k3_lattice3(sK1),sK0,X2) )
          & m1_subset_1(X2,u1_struct_0(k3_lattice3(sK1))) )
      & l3_lattices(sK1)
      & v10_lattices(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X2] :
        ( ( ~ r4_lattice3(sK1,k5_lattice3(sK1,X2),sK0)
          | ~ r2_lattice3(k3_lattice3(sK1),sK0,X2) )
        & ( r4_lattice3(sK1,k5_lattice3(sK1,X2),sK0)
          | r2_lattice3(k3_lattice3(sK1),sK0,X2) )
        & m1_subset_1(X2,u1_struct_0(k3_lattice3(sK1))) )
   => ( ( ~ r4_lattice3(sK1,k5_lattice3(sK1,sK2),sK0)
        | ~ r2_lattice3(k3_lattice3(sK1),sK0,sK2) )
      & ( r4_lattice3(sK1,k5_lattice3(sK1,sK2),sK0)
        | r2_lattice3(k3_lattice3(sK1),sK0,sK2) )
      & m1_subset_1(sK2,u1_struct_0(k3_lattice3(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r4_lattice3(X1,k5_lattice3(X1,X2),X0)
            | ~ r2_lattice3(k3_lattice3(X1),X0,X2) )
          & ( r4_lattice3(X1,k5_lattice3(X1,X2),X0)
            | r2_lattice3(k3_lattice3(X1),X0,X2) )
          & m1_subset_1(X2,u1_struct_0(k3_lattice3(X1))) )
      & l3_lattices(X1)
      & v10_lattices(X1)
      & ~ v2_struct_0(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r4_lattice3(X1,k5_lattice3(X1,X2),X0)
            | ~ r2_lattice3(k3_lattice3(X1),X0,X2) )
          & ( r4_lattice3(X1,k5_lattice3(X1,X2),X0)
            | r2_lattice3(k3_lattice3(X1),X0,X2) )
          & m1_subset_1(X2,u1_struct_0(k3_lattice3(X1))) )
      & l3_lattices(X1)
      & v10_lattices(X1)
      & ~ v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r2_lattice3(k3_lattice3(X1),X0,X2)
          <~> r4_lattice3(X1,k5_lattice3(X1,X2),X0) )
          & m1_subset_1(X2,u1_struct_0(k3_lattice3(X1))) )
      & l3_lattices(X1)
      & v10_lattices(X1)
      & ~ v2_struct_0(X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r2_lattice3(k3_lattice3(X1),X0,X2)
          <~> r4_lattice3(X1,k5_lattice3(X1,X2),X0) )
          & m1_subset_1(X2,u1_struct_0(k3_lattice3(X1))) )
      & l3_lattices(X1)
      & v10_lattices(X1)
      & ~ v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( l3_lattices(X1)
          & v10_lattices(X1)
          & ~ v2_struct_0(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(k3_lattice3(X1)))
           => ( r2_lattice3(k3_lattice3(X1),X0,X2)
            <=> r4_lattice3(X1,k5_lattice3(X1,X2),X0) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( ( l3_lattices(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(k3_lattice3(X1)))
         => ( r2_lattice3(k3_lattice3(X1),X0,X2)
          <=> r4_lattice3(X1,k5_lattice3(X1,X2),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_lattice3)).

fof(f27,plain,
    ( r4_lattice3(sK1,k5_lattice3(sK1,sK2),sK0)
    | r2_lattice3(k3_lattice3(sK1),sK0,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f50,plain,(
    ! [X1] :
      ( ~ r2_lattice3(k3_lattice3(sK1),X1,sK2)
      | r4_lattice3(sK1,sK2,X1)
      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
      | ~ l3_lattices(sK1)
      | ~ v10_lattices(sK1)
      | v2_struct_0(sK1) ) ),
    inference(superposition,[],[f30,f43])).

fof(f43,plain,(
    sK2 = k4_lattice3(sK1,sK2) ),
    inference(forward_demodulation,[],[f40,f34])).

fof(f40,plain,(
    k5_lattice3(sK1,sK2) = k4_lattice3(sK1,k5_lattice3(sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f23,f24,f25,f35,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | k4_lattice3(X0,X1) = X1
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattice3(X0,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattice3(X0,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k4_lattice3(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_lattice3)).

fof(f35,plain,(
    m1_subset_1(k5_lattice3(sK1,sK2),u1_struct_0(sK1)) ),
    inference(unit_resulting_resolution,[],[f23,f24,f25,f26,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_lattice3(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_lattice3(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_lattice3(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
        & l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattice3)).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2))
      | r4_lattice3(X1,X2,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r4_lattice3(X1,X2,X0)
              | ~ r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2)) )
            & ( r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2))
              | ~ r4_lattice3(X1,X2,X0) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X1)) )
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r4_lattice3(X1,X2,X0)
          <=> r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2)) )
          | ~ m1_subset_1(X2,u1_struct_0(X1)) )
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r4_lattice3(X1,X2,X0)
          <=> r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2)) )
          | ~ m1_subset_1(X2,u1_struct_0(X1)) )
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( r4_lattice3(X1,X2,X0)
          <=> r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_lattice3)).

fof(f55,plain,
    ( ~ r4_lattice3(sK1,sK2,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l3_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1) ),
    inference(duplicate_literal_removal,[],[f54])).

fof(f54,plain,
    ( ~ r4_lattice3(sK1,sK2,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l3_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ r4_lattice3(sK1,sK2,sK0) ),
    inference(resolution,[],[f49,f46])).

fof(f46,plain,
    ( ~ r2_lattice3(k3_lattice3(sK1),sK0,sK2)
    | ~ r4_lattice3(sK1,sK2,sK0) ),
    inference(superposition,[],[f28,f34])).

fof(f28,plain,
    ( ~ r4_lattice3(sK1,k5_lattice3(sK1,sK2),sK0)
    | ~ r2_lattice3(k3_lattice3(sK1),sK0,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f49,plain,(
    ! [X0] :
      ( r2_lattice3(k3_lattice3(sK1),X0,sK2)
      | ~ r4_lattice3(sK1,sK2,X0)
      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
      | ~ l3_lattices(sK1)
      | ~ v10_lattices(sK1)
      | v2_struct_0(sK1) ) ),
    inference(superposition,[],[f29,f43])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2))
      | ~ r4_lattice3(X1,X2,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f42,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(superposition,[],[f35,f34])).

fof(f25,plain,(
    l3_lattices(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f24,plain,(
    v10_lattices(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f23,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f21])).

%------------------------------------------------------------------------------
