%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1506+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:58 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   38 (  87 expanded)
%              Number of leaves         :    4 (  15 expanded)
%              Depth                    :   12
%              Number of atoms          :  143 ( 456 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f58,plain,(
    $false ),
    inference(subsumption_resolution,[],[f57,f15])).

fof(f15,plain,(
    ~ r3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_lattices(X0,X1,k16_lattice3(X0,X2))
              & r3_lattice3(X0,X1,X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_lattices(X0,X1,k16_lattice3(X0,X2))
              & r3_lattice3(X0,X1,X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( r3_lattice3(X0,X1,X2)
               => r3_lattices(X0,X1,k16_lattice3(X0,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r3_lattice3(X0,X1,X2)
             => r3_lattices(X0,X1,k16_lattice3(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_lattice3)).

fof(f57,plain,(
    r3_lattices(sK0,sK1,k16_lattice3(sK0,sK2)) ),
    inference(forward_demodulation,[],[f56,f30])).

fof(f30,plain,(
    ! [X0] : k16_lattice3(sK0,X0) = k15_lattice3(sK0,a_2_1_lattice3(sK0,X0)) ),
    inference(subsumption_resolution,[],[f29,f17])).

fof(f17,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f29,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | k16_lattice3(sK0,X0) = k15_lattice3(sK0,a_2_1_lattice3(sK0,X0)) ) ),
    inference(resolution,[],[f20,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] : k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] : k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] : k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d22_lattice3)).

fof(f20,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f56,plain,(
    r3_lattices(sK0,sK1,k15_lattice3(sK0,a_2_1_lattice3(sK0,sK2))) ),
    inference(resolution,[],[f40,f34])).

fof(f34,plain,(
    r2_hidden(sK1,a_2_1_lattice3(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f33,f17])).

fof(f33,plain,
    ( v2_struct_0(sK0)
    | r2_hidden(sK1,a_2_1_lattice3(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f32,f16])).

fof(f16,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f32,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r2_hidden(sK1,a_2_1_lattice3(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f31,f20])).

fof(f31,plain,
    ( ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r2_hidden(sK1,a_2_1_lattice3(sK0,sK2)) ),
    inference(resolution,[],[f14,f28])).

fof(f28,plain,(
    ! [X2,X3,X1] :
      ( ~ r3_lattice3(X1,X3,X2)
      | ~ l3_lattices(X1)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | v2_struct_0(X1)
      | r2_hidden(X3,a_2_1_lattice3(X1,X2)) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X1)
      | ~ l3_lattices(X1)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | X0 != X3
      | ~ r3_lattice3(X1,X3,X2)
      | r2_hidden(X0,a_2_1_lattice3(X1,X2)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( l3_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_lattice3)).

fof(f14,plain,(
    r3_lattice3(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f40,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK1,X0)
      | r3_lattices(sK0,sK1,k15_lattice3(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f39,f17])).

fof(f39,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ r2_hidden(sK1,X0)
      | r3_lattices(sK0,sK1,k15_lattice3(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f38,f20])).

fof(f38,plain,(
    ! [X0] :
      ( ~ l3_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ r2_hidden(sK1,X0)
      | r3_lattices(sK0,sK1,k15_lattice3(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f37,f19])).

fof(f19,plain,(
    v4_lattice3(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v4_lattice3(sK0)
      | ~ l3_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ r2_hidden(sK1,X0)
      | r3_lattices(sK0,sK1,k15_lattice3(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f35,f18])).

fof(f18,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v10_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ l3_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ r2_hidden(sK1,X0)
      | r3_lattices(sK0,sK1,k15_lattice3(sK0,X0)) ) ),
    inference(resolution,[],[f16,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ r2_hidden(X1,X2)
      | r3_lattices(X0,X1,k15_lattice3(X0,X2)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
                & r3_lattices(X0,X1,k15_lattice3(X0,X2)) )
              | ~ r2_hidden(X1,X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
                & r3_lattices(X0,X1,k15_lattice3(X0,X2)) )
              | ~ r2_hidden(X1,X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r2_hidden(X1,X2)
             => ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
                & r3_lattices(X0,X1,k15_lattice3(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_lattice3)).

%------------------------------------------------------------------------------
