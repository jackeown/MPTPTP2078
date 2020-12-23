%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1496+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:58 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 806 expanded)
%              Number of leaves         :    7 ( 212 expanded)
%              Depth                    :   29
%              Number of atoms          :  281 (5496 expanded)
%              Number of equality atoms :   12 (  68 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f70,plain,(
    $false ),
    inference(subsumption_resolution,[],[f69,f23])).

fof(f23,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ( ~ r3_lattice3(sK1,k5_lattice3(sK1,sK2),sK0)
      | ~ r1_lattice3(k3_lattice3(sK1),sK0,sK2) )
    & ( r3_lattice3(sK1,k5_lattice3(sK1,sK2),sK0)
      | r1_lattice3(k3_lattice3(sK1),sK0,sK2) )
    & m1_subset_1(sK2,u1_struct_0(k3_lattice3(sK1)))
    & l3_lattices(sK1)
    & v10_lattices(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f20,f19])).

fof(f19,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r3_lattice3(X1,k5_lattice3(X1,X2),X0)
              | ~ r1_lattice3(k3_lattice3(X1),X0,X2) )
            & ( r3_lattice3(X1,k5_lattice3(X1,X2),X0)
              | r1_lattice3(k3_lattice3(X1),X0,X2) )
            & m1_subset_1(X2,u1_struct_0(k3_lattice3(X1))) )
        & l3_lattices(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ( ~ r3_lattice3(sK1,k5_lattice3(sK1,X2),sK0)
            | ~ r1_lattice3(k3_lattice3(sK1),sK0,X2) )
          & ( r3_lattice3(sK1,k5_lattice3(sK1,X2),sK0)
            | r1_lattice3(k3_lattice3(sK1),sK0,X2) )
          & m1_subset_1(X2,u1_struct_0(k3_lattice3(sK1))) )
      & l3_lattices(sK1)
      & v10_lattices(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X2] :
        ( ( ~ r3_lattice3(sK1,k5_lattice3(sK1,X2),sK0)
          | ~ r1_lattice3(k3_lattice3(sK1),sK0,X2) )
        & ( r3_lattice3(sK1,k5_lattice3(sK1,X2),sK0)
          | r1_lattice3(k3_lattice3(sK1),sK0,X2) )
        & m1_subset_1(X2,u1_struct_0(k3_lattice3(sK1))) )
   => ( ( ~ r3_lattice3(sK1,k5_lattice3(sK1,sK2),sK0)
        | ~ r1_lattice3(k3_lattice3(sK1),sK0,sK2) )
      & ( r3_lattice3(sK1,k5_lattice3(sK1,sK2),sK0)
        | r1_lattice3(k3_lattice3(sK1),sK0,sK2) )
      & m1_subset_1(sK2,u1_struct_0(k3_lattice3(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r3_lattice3(X1,k5_lattice3(X1,X2),X0)
            | ~ r1_lattice3(k3_lattice3(X1),X0,X2) )
          & ( r3_lattice3(X1,k5_lattice3(X1,X2),X0)
            | r1_lattice3(k3_lattice3(X1),X0,X2) )
          & m1_subset_1(X2,u1_struct_0(k3_lattice3(X1))) )
      & l3_lattices(X1)
      & v10_lattices(X1)
      & ~ v2_struct_0(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r3_lattice3(X1,k5_lattice3(X1,X2),X0)
            | ~ r1_lattice3(k3_lattice3(X1),X0,X2) )
          & ( r3_lattice3(X1,k5_lattice3(X1,X2),X0)
            | r1_lattice3(k3_lattice3(X1),X0,X2) )
          & m1_subset_1(X2,u1_struct_0(k3_lattice3(X1))) )
      & l3_lattices(X1)
      & v10_lattices(X1)
      & ~ v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_lattice3(k3_lattice3(X1),X0,X2)
          <~> r3_lattice3(X1,k5_lattice3(X1,X2),X0) )
          & m1_subset_1(X2,u1_struct_0(k3_lattice3(X1))) )
      & l3_lattices(X1)
      & v10_lattices(X1)
      & ~ v2_struct_0(X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_lattice3(k3_lattice3(X1),X0,X2)
          <~> r3_lattice3(X1,k5_lattice3(X1,X2),X0) )
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
           => ( r1_lattice3(k3_lattice3(X1),X0,X2)
            <=> r3_lattice3(X1,k5_lattice3(X1,X2),X0) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( ( l3_lattices(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(k3_lattice3(X1)))
         => ( r1_lattice3(k3_lattice3(X1),X0,X2)
          <=> r3_lattice3(X1,k5_lattice3(X1,X2),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_lattice3)).

fof(f69,plain,(
    v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f68,f24])).

fof(f24,plain,(
    v10_lattices(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f68,plain,
    ( ~ v10_lattices(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f67,f25])).

fof(f25,plain,(
    l3_lattices(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f67,plain,
    ( ~ l3_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f66,f44])).

fof(f44,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f43,f26])).

fof(f26,plain,(
    m1_subset_1(sK2,u1_struct_0(k3_lattice3(sK1))) ),
    inference(cnf_transformation,[],[f21])).

fof(f43,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(k3_lattice3(sK1))) ),
    inference(superposition,[],[f42,f37])).

fof(f37,plain,(
    sK2 = k5_lattice3(sK1,sK2) ),
    inference(resolution,[],[f36,f26])).

fof(f36,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(sK1)))
      | k5_lattice3(sK1,X0) = X0 ) ),
    inference(subsumption_resolution,[],[f35,f23])).

fof(f35,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(sK1)))
      | k5_lattice3(sK1,X0) = X0
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f34,f24])).

fof(f34,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(sK1)))
      | k5_lattice3(sK1,X0) = X0
      | ~ v10_lattices(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f30,f25])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
      | k5_lattice3(X0,X1) = X1
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_lattice3(X0,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0))) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
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

fof(f42,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattice3(sK1,X0),u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(sK1))) ) ),
    inference(subsumption_resolution,[],[f41,f23])).

fof(f41,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(sK1)))
      | m1_subset_1(k5_lattice3(sK1,X0),u1_struct_0(sK1))
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f40,f24])).

fof(f40,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(sK1)))
      | m1_subset_1(k5_lattice3(sK1,X0),u1_struct_0(sK1))
      | ~ v10_lattices(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f31,f25])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
      | m1_subset_1(k5_lattice3(X0,X1),u1_struct_0(X0))
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_lattice3(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
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

fof(f66,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l3_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f65,f56])).

fof(f56,plain,(
    ~ r1_lattice3(k3_lattice3(sK1),sK0,sK2) ),
    inference(subsumption_resolution,[],[f39,f55])).

fof(f55,plain,(
    r3_lattice3(sK1,sK2,sK0) ),
    inference(subsumption_resolution,[],[f54,f44])).

fof(f54,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | r3_lattice3(sK1,sK2,sK0) ),
    inference(duplicate_literal_removal,[],[f53])).

fof(f53,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | r3_lattice3(sK1,sK2,sK0)
    | r3_lattice3(sK1,sK2,sK0) ),
    inference(resolution,[],[f52,f38])).

fof(f38,plain,
    ( r1_lattice3(k3_lattice3(sK1),sK0,sK2)
    | r3_lattice3(sK1,sK2,sK0) ),
    inference(backward_demodulation,[],[f27,f37])).

fof(f27,plain,
    ( r1_lattice3(k3_lattice3(sK1),sK0,sK2)
    | r3_lattice3(sK1,k5_lattice3(sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_lattice3(k3_lattice3(sK1),X1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | r3_lattice3(sK1,X0,X1) ) ),
    inference(subsumption_resolution,[],[f51,f23])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_lattice3(k3_lattice3(sK1),X1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | r3_lattice3(sK1,X0,X1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f50,f24])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_lattice3(k3_lattice3(sK1),X1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | r3_lattice3(sK1,X0,X1)
      | ~ v10_lattices(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f49,f25])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_lattice3(k3_lattice3(sK1),X1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | r3_lattice3(sK1,X0,X1)
      | ~ l3_lattices(sK1)
      | ~ v10_lattices(sK1)
      | v2_struct_0(sK1) ) ),
    inference(duplicate_literal_removal,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_lattice3(k3_lattice3(sK1),X1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | r3_lattice3(sK1,X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ l3_lattices(sK1)
      | ~ v10_lattices(sK1)
      | v2_struct_0(sK1) ) ),
    inference(superposition,[],[f47,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k4_lattice3(X0,X1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattice3(X0,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
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

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_lattice3(k3_lattice3(sK1),X0,k4_lattice3(sK1,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | r3_lattice3(sK1,X1,X0) ) ),
    inference(subsumption_resolution,[],[f46,f23])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_lattice3(k3_lattice3(sK1),X0,k4_lattice3(sK1,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | r3_lattice3(sK1,X1,X0)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f45,f24])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_lattice3(k3_lattice3(sK1),X0,k4_lattice3(sK1,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | r3_lattice3(sK1,X1,X0)
      | ~ v10_lattices(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f33,f25])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ l3_lattices(X1)
      | ~ r1_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | r3_lattice3(X1,X2,X0)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r3_lattice3(X1,X2,X0)
              | ~ r1_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2)) )
            & ( r1_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2))
              | ~ r3_lattice3(X1,X2,X0) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X1)) )
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r3_lattice3(X1,X2,X0)
          <=> r1_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2)) )
          | ~ m1_subset_1(X2,u1_struct_0(X1)) )
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r3_lattice3(X1,X2,X0)
          <=> r1_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2)) )
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
         => ( r3_lattice3(X1,X2,X0)
          <=> r1_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_lattice3)).

fof(f39,plain,
    ( ~ r3_lattice3(sK1,sK2,sK0)
    | ~ r1_lattice3(k3_lattice3(sK1),sK0,sK2) ),
    inference(backward_demodulation,[],[f28,f37])).

fof(f28,plain,
    ( ~ r3_lattice3(sK1,k5_lattice3(sK1,sK2),sK0)
    | ~ r1_lattice3(k3_lattice3(sK1),sK0,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f65,plain,
    ( r1_lattice3(k3_lattice3(sK1),sK0,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l3_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1) ),
    inference(superposition,[],[f62,f29])).

fof(f62,plain,(
    r1_lattice3(k3_lattice3(sK1),sK0,k4_lattice3(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f61,f23])).

fof(f61,plain,
    ( r1_lattice3(k3_lattice3(sK1),sK0,k4_lattice3(sK1,sK2))
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f60,f24])).

fof(f60,plain,
    ( r1_lattice3(k3_lattice3(sK1),sK0,k4_lattice3(sK1,sK2))
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f59,f25])).

fof(f59,plain,
    ( r1_lattice3(k3_lattice3(sK1),sK0,k4_lattice3(sK1,sK2))
    | ~ l3_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f58,f44])).

fof(f58,plain,
    ( r1_lattice3(k3_lattice3(sK1),sK0,k4_lattice3(sK1,sK2))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l3_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f55,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_lattice3(X1,X2,X0)
      | r1_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f22])).

%------------------------------------------------------------------------------
