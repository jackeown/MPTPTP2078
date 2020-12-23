%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1199+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:28 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 180 expanded)
%              Number of leaves         :    4 (  31 expanded)
%              Depth                    :   13
%              Number of atoms          :  192 (1058 expanded)
%              Number of equality atoms :   46 ( 154 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f68,plain,(
    $false ),
    inference(subsumption_resolution,[],[f67,f17])).

fof(f17,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & r1_lattices(X0,X2,X1)
              & r1_lattices(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l2_lattices(X0)
      & v4_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & r1_lattices(X0,X2,X1)
              & r1_lattices(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l2_lattices(X0)
      & v4_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l2_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( ( r1_lattices(X0,X2,X1)
                    & r1_lattices(X0,X1,X2) )
                 => X1 = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r1_lattices(X0,X2,X1)
                  & r1_lattices(X0,X1,X2) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_lattices)).

fof(f67,plain,(
    sK1 = sK2 ),
    inference(forward_demodulation,[],[f66,f60])).

fof(f60,plain,(
    sK1 = k3_lattices(sK0,sK2,sK1) ),
    inference(forward_demodulation,[],[f59,f41])).

fof(f41,plain,(
    sK1 = k1_lattices(sK0,sK2,sK1) ),
    inference(subsumption_resolution,[],[f40,f19])).

fof(f19,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f40,plain,
    ( sK1 = k1_lattices(sK0,sK2,sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f39,f18])).

fof(f18,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f39,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | sK1 = k1_lattices(sK0,sK2,sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f38,f14])).

fof(f14,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f38,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | sK1 = k1_lattices(sK0,sK2,sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f33,f21])).

fof(f21,plain,(
    l2_lattices(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f33,plain,
    ( ~ l2_lattices(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | sK1 = k1_lattices(sK0,sK2,sK1)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f23,f16])).

fof(f16,plain,(
    r1_lattices(sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X1,X2)
      | ~ l2_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_lattices(X0,X1,X2) = X2
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_lattices)).

fof(f59,plain,(
    k1_lattices(sK0,sK2,sK1) = k3_lattices(sK0,sK2,sK1) ),
    inference(resolution,[],[f46,f18])).

fof(f46,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k1_lattices(sK0,sK2,X0) = k3_lattices(sK0,sK2,X0) ) ),
    inference(subsumption_resolution,[],[f45,f19])).

fof(f45,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k1_lattices(sK0,sK2,X0) = k3_lattices(sK0,sK2,X0) ) ),
    inference(subsumption_resolution,[],[f44,f21])).

fof(f44,plain,(
    ! [X0] :
      ( ~ l2_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k1_lattices(sK0,sK2,X0) = k3_lattices(sK0,sK2,X0) ) ),
    inference(subsumption_resolution,[],[f42,f20])).

fof(f20,plain,(
    v4_lattices(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v4_lattices(sK0)
      | ~ l2_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k1_lattices(sK0,sK2,X0) = k3_lattices(sK0,sK2,X0) ) ),
    inference(resolution,[],[f24,f14])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v4_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_lattices)).

fof(f66,plain,(
    sK2 = k3_lattices(sK0,sK2,sK1) ),
    inference(forward_demodulation,[],[f65,f63])).

fof(f63,plain,(
    sK2 = k3_lattices(sK0,sK1,sK2) ),
    inference(forward_demodulation,[],[f61,f37])).

fof(f37,plain,(
    sK2 = k1_lattices(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f36,f19])).

fof(f36,plain,
    ( sK2 = k1_lattices(sK0,sK1,sK2)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f35,f14])).

fof(f35,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | sK2 = k1_lattices(sK0,sK1,sK2)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f34,f18])).

fof(f34,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | sK2 = k1_lattices(sK0,sK1,sK2)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f32,f21])).

fof(f32,plain,
    ( ~ l2_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | sK2 = k1_lattices(sK0,sK1,sK2)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f23,f15])).

fof(f15,plain,(
    r1_lattices(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f61,plain,(
    k1_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK1,sK2) ),
    inference(resolution,[],[f49,f14])).

fof(f49,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k1_lattices(sK0,sK1,X1) = k3_lattices(sK0,sK1,X1) ) ),
    inference(subsumption_resolution,[],[f48,f19])).

fof(f48,plain,(
    ! [X1] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k1_lattices(sK0,sK1,X1) = k3_lattices(sK0,sK1,X1) ) ),
    inference(subsumption_resolution,[],[f47,f21])).

fof(f47,plain,(
    ! [X1] :
      ( ~ l2_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k1_lattices(sK0,sK1,X1) = k3_lattices(sK0,sK1,X1) ) ),
    inference(subsumption_resolution,[],[f43,f20])).

fof(f43,plain,(
    ! [X1] :
      ( ~ v4_lattices(sK0)
      | ~ l2_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k1_lattices(sK0,sK1,X1) = k3_lattices(sK0,sK1,X1) ) ),
    inference(resolution,[],[f24,f18])).

fof(f65,plain,(
    k3_lattices(sK0,sK2,sK1) = k3_lattices(sK0,sK1,sK2) ),
    inference(resolution,[],[f54,f18])).

fof(f54,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k3_lattices(sK0,sK2,X0) = k3_lattices(sK0,X0,sK2) ) ),
    inference(subsumption_resolution,[],[f53,f19])).

fof(f53,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k3_lattices(sK0,sK2,X0) = k3_lattices(sK0,X0,sK2) ) ),
    inference(subsumption_resolution,[],[f52,f21])).

fof(f52,plain,(
    ! [X0] :
      ( ~ l2_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k3_lattices(sK0,sK2,X0) = k3_lattices(sK0,X0,sK2) ) ),
    inference(subsumption_resolution,[],[f50,f20])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v4_lattices(sK0)
      | ~ l2_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k3_lattices(sK0,sK2,X0) = k3_lattices(sK0,X0,sK2) ) ),
    inference(resolution,[],[f25,f14])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v4_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_lattices)).

%------------------------------------------------------------------------------
