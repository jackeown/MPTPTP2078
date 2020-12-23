%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:45 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 241 expanded)
%              Number of leaves         :    7 (  41 expanded)
%              Depth                    :   19
%              Number of atoms          :  321 (1405 expanded)
%              Number of equality atoms :   39 (  42 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f167,plain,(
    $false ),
    inference(subsumption_resolution,[],[f166,f160])).

fof(f160,plain,(
    k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,sK2),sK1) ),
    inference(backward_demodulation,[],[f135,f159])).

fof(f159,plain,(
    k5_lattices(sK0) = k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f158,f31])).

fof(f31,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))
              & r3_lattices(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))
              & r3_lattices(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v17_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r3_lattices(X0,X1,X2)
                 => r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r3_lattices(X0,X1,X2)
               => r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_lattices)).

fof(f158,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | k5_lattices(sK0) = k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)) ),
    inference(resolution,[],[f122,f29])).

fof(f29,plain,(
    r3_lattices(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f122,plain,(
    ! [X0] :
      ( ~ r3_lattices(sK0,X0,sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k5_lattices(sK0) = k4_lattices(sK0,X0,k7_lattices(sK0,sK2)) ) ),
    inference(subsumption_resolution,[],[f121,f32])).

fof(f32,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f121,plain,(
    ! [X0] :
      ( ~ r3_lattices(sK0,X0,sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | k5_lattices(sK0) = k4_lattices(sK0,X0,k7_lattices(sK0,sK2)) ) ),
    inference(subsumption_resolution,[],[f120,f63])).

fof(f63,plain,(
    m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f62,f32])).

fof(f62,plain,
    ( v2_struct_0(sK0)
    | m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f50,f35])).

fof(f35,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f50,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) ),
    inference(resolution,[],[f28,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_lattices)).

fof(f28,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f120,plain,(
    ! [X0] :
      ( ~ r3_lattices(sK0,X0,sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | k5_lattices(sK0) = k4_lattices(sK0,X0,k7_lattices(sK0,sK2)) ) ),
    inference(subsumption_resolution,[],[f119,f35])).

fof(f119,plain,(
    ! [X0] :
      ( ~ r3_lattices(sK0,X0,sK2)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | k5_lattices(sK0) = k4_lattices(sK0,X0,k7_lattices(sK0,sK2)) ) ),
    inference(subsumption_resolution,[],[f118,f34])).

fof(f34,plain,(
    v17_lattices(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f118,plain,(
    ! [X0] :
      ( ~ r3_lattices(sK0,X0,sK2)
      | ~ v17_lattices(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | k5_lattices(sK0) = k4_lattices(sK0,X0,k7_lattices(sK0,sK2)) ) ),
    inference(subsumption_resolution,[],[f117,f33])).

fof(f33,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f117,plain,(
    ! [X0] :
      ( ~ r3_lattices(sK0,X0,sK2)
      | ~ v10_lattices(sK0)
      | ~ v17_lattices(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | k5_lattices(sK0) = k4_lattices(sK0,X0,k7_lattices(sK0,sK2)) ) ),
    inference(superposition,[],[f38,f61])).

fof(f61,plain,(
    sK2 = k7_lattices(sK0,k7_lattices(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f60,f32])).

fof(f60,plain,
    ( v2_struct_0(sK0)
    | sK2 = k7_lattices(sK0,k7_lattices(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f59,f35])).

fof(f59,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | sK2 = k7_lattices(sK0,k7_lattices(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f58,f34])).

fof(f58,plain,
    ( ~ v17_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | sK2 = k7_lattices(sK0,k7_lattices(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f49,f33])).

fof(f49,plain,
    ( ~ v10_lattices(sK0)
    | ~ v17_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | sK2 = k7_lattices(sK0,k7_lattices(sK0,sK2)) ),
    inference(resolution,[],[f28,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v10_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | k7_lattices(X0,k7_lattices(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_lattices(X0,k7_lattices(X0,X1)) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_lattices(X0,k7_lattices(X0,X1)) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k7_lattices(X0,k7_lattices(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_lattices)).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_lattices(X0,X1,k7_lattices(X0,X2))
      | ~ v10_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | k4_lattices(X0,X1,X2) = k5_lattices(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_lattices(X0,X1,X2) = k5_lattices(X0)
              <=> r3_lattices(X0,X1,k7_lattices(X0,X2)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_lattices(X0,X1,X2) = k5_lattices(X0)
              <=> r3_lattices(X0,X1,k7_lattices(X0,X2)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( k4_lattices(X0,X1,X2) = k5_lattices(X0)
              <=> r3_lattices(X0,X1,k7_lattices(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_lattices)).

fof(f135,plain,(
    k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)) = k4_lattices(sK0,k7_lattices(sK0,sK2),sK1) ),
    inference(resolution,[],[f70,f63])).

fof(f70,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k4_lattices(sK0,sK1,X0) = k4_lattices(sK0,X0,sK1) ) ),
    inference(subsumption_resolution,[],[f69,f32])).

fof(f69,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k4_lattices(sK0,sK1,X0) = k4_lattices(sK0,X0,sK1) ) ),
    inference(subsumption_resolution,[],[f68,f46])).

fof(f46,plain,(
    l1_lattices(sK0) ),
    inference(resolution,[],[f35,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | l1_lattices(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => l1_lattices(X0) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f68,plain,(
    ! [X0] :
      ( ~ l1_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k4_lattices(sK0,sK1,X0) = k4_lattices(sK0,X0,sK1) ) ),
    inference(subsumption_resolution,[],[f64,f45])).

fof(f45,plain,(
    v6_lattices(sK0) ),
    inference(subsumption_resolution,[],[f44,f35])).

fof(f44,plain,
    ( ~ l3_lattices(sK0)
    | v6_lattices(sK0) ),
    inference(subsumption_resolution,[],[f43,f32])).

fof(f43,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | v6_lattices(sK0) ),
    inference(resolution,[],[f33,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v6_lattices(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v6_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v7_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v8_lattices(X0)
          & v7_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v7_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).

fof(f64,plain,(
    ! [X0] :
      ( ~ v6_lattices(sK0)
      | ~ l1_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k4_lattices(sK0,sK1,X0) = k4_lattices(sK0,X0,sK1) ) ),
    inference(resolution,[],[f31,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v6_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_lattices)).

fof(f166,plain,(
    k5_lattices(sK0) != k4_lattices(sK0,k7_lattices(sK0,sK2),sK1) ),
    inference(subsumption_resolution,[],[f162,f30])).

fof(f30,plain,(
    ~ r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f162,plain,
    ( r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))
    | k5_lattices(sK0) != k4_lattices(sK0,k7_lattices(sK0,sK2),sK1) ),
    inference(resolution,[],[f91,f31])).

fof(f91,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,X1))
      | k5_lattices(sK0) != k4_lattices(sK0,k7_lattices(sK0,sK2),X1) ) ),
    inference(subsumption_resolution,[],[f90,f32])).

fof(f90,plain,(
    ! [X1] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,X1))
      | k5_lattices(sK0) != k4_lattices(sK0,k7_lattices(sK0,sK2),X1) ) ),
    inference(subsumption_resolution,[],[f89,f35])).

fof(f89,plain,(
    ! [X1] :
      ( ~ l3_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,X1))
      | k5_lattices(sK0) != k4_lattices(sK0,k7_lattices(sK0,sK2),X1) ) ),
    inference(subsumption_resolution,[],[f88,f34])).

fof(f88,plain,(
    ! [X1] :
      ( ~ v17_lattices(sK0)
      | ~ l3_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,X1))
      | k5_lattices(sK0) != k4_lattices(sK0,k7_lattices(sK0,sK2),X1) ) ),
    inference(subsumption_resolution,[],[f82,f33])).

fof(f82,plain,(
    ! [X1] :
      ( ~ v10_lattices(sK0)
      | ~ v17_lattices(sK0)
      | ~ l3_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,X1))
      | k5_lattices(sK0) != k4_lattices(sK0,k7_lattices(sK0,sK2),X1) ) ),
    inference(resolution,[],[f63,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v10_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r3_lattices(X0,X1,k7_lattices(X0,X2))
      | k4_lattices(X0,X1,X2) != k5_lattices(X0) ) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:21:32 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.44  % (29820)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.46  % (29830)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.22/0.46  % (29823)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.47  % (29816)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.48  % (29837)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.48  % (29837)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f167,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(subsumption_resolution,[],[f166,f160])).
% 0.22/0.48  fof(f160,plain,(
% 0.22/0.48    k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,sK2),sK1)),
% 0.22/0.48    inference(backward_demodulation,[],[f135,f159])).
% 0.22/0.48  fof(f159,plain,(
% 0.22/0.48    k5_lattices(sK0) = k4_lattices(sK0,sK1,k7_lattices(sK0,sK2))),
% 0.22/0.48    inference(subsumption_resolution,[],[f158,f31])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.48    inference(cnf_transformation,[],[f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (? [X2] : (~r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) & r3_lattices(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (? [X2] : ((~r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) & r3_lattices(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,negated_conjecture,(
% 0.22/0.48    ~! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_lattices(X0,X1,X2) => r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))))))),
% 0.22/0.48    inference(negated_conjecture,[],[f7])).
% 0.22/0.48  fof(f7,conjecture,(
% 0.22/0.48    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_lattices(X0,X1,X2) => r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_lattices)).
% 0.22/0.48  fof(f158,plain,(
% 0.22/0.48    ~m1_subset_1(sK1,u1_struct_0(sK0)) | k5_lattices(sK0) = k4_lattices(sK0,sK1,k7_lattices(sK0,sK2))),
% 0.22/0.48    inference(resolution,[],[f122,f29])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    r3_lattices(sK0,sK1,sK2)),
% 0.22/0.48    inference(cnf_transformation,[],[f16])).
% 0.22/0.48  fof(f122,plain,(
% 0.22/0.48    ( ! [X0] : (~r3_lattices(sK0,X0,sK2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k5_lattices(sK0) = k4_lattices(sK0,X0,k7_lattices(sK0,sK2))) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f121,f32])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    ~v2_struct_0(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f16])).
% 0.22/0.48  fof(f121,plain,(
% 0.22/0.48    ( ! [X0] : (~r3_lattices(sK0,X0,sK2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0) | k5_lattices(sK0) = k4_lattices(sK0,X0,k7_lattices(sK0,sK2))) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f120,f63])).
% 0.22/0.48  fof(f63,plain,(
% 0.22/0.48    m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))),
% 0.22/0.48    inference(subsumption_resolution,[],[f62,f32])).
% 0.22/0.48  fof(f62,plain,(
% 0.22/0.48    v2_struct_0(sK0) | m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))),
% 0.22/0.48    inference(subsumption_resolution,[],[f50,f35])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    l3_lattices(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f16])).
% 0.22/0.48  fof(f50,plain,(
% 0.22/0.48    ~l3_lattices(sK0) | v2_struct_0(sK0) | m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))),
% 0.22/0.48    inference(resolution,[],[f28,f36])).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0) | m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_lattices)).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.22/0.48    inference(cnf_transformation,[],[f16])).
% 0.22/0.48  fof(f120,plain,(
% 0.22/0.48    ( ! [X0] : (~r3_lattices(sK0,X0,sK2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) | v2_struct_0(sK0) | k5_lattices(sK0) = k4_lattices(sK0,X0,k7_lattices(sK0,sK2))) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f119,f35])).
% 0.22/0.48  fof(f119,plain,(
% 0.22/0.48    ( ! [X0] : (~r3_lattices(sK0,X0,sK2) | ~l3_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) | v2_struct_0(sK0) | k5_lattices(sK0) = k4_lattices(sK0,X0,k7_lattices(sK0,sK2))) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f118,f34])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    v17_lattices(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f16])).
% 0.22/0.48  fof(f118,plain,(
% 0.22/0.48    ( ! [X0] : (~r3_lattices(sK0,X0,sK2) | ~v17_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) | v2_struct_0(sK0) | k5_lattices(sK0) = k4_lattices(sK0,X0,k7_lattices(sK0,sK2))) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f117,f33])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    v10_lattices(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f16])).
% 0.22/0.48  fof(f117,plain,(
% 0.22/0.48    ( ! [X0] : (~r3_lattices(sK0,X0,sK2) | ~v10_lattices(sK0) | ~v17_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) | v2_struct_0(sK0) | k5_lattices(sK0) = k4_lattices(sK0,X0,k7_lattices(sK0,sK2))) )),
% 0.22/0.48    inference(superposition,[],[f38,f61])).
% 0.22/0.48  fof(f61,plain,(
% 0.22/0.48    sK2 = k7_lattices(sK0,k7_lattices(sK0,sK2))),
% 0.22/0.48    inference(subsumption_resolution,[],[f60,f32])).
% 0.22/0.48  fof(f60,plain,(
% 0.22/0.48    v2_struct_0(sK0) | sK2 = k7_lattices(sK0,k7_lattices(sK0,sK2))),
% 0.22/0.48    inference(subsumption_resolution,[],[f59,f35])).
% 0.22/0.48  fof(f59,plain,(
% 0.22/0.48    ~l3_lattices(sK0) | v2_struct_0(sK0) | sK2 = k7_lattices(sK0,k7_lattices(sK0,sK2))),
% 0.22/0.48    inference(subsumption_resolution,[],[f58,f34])).
% 0.22/0.48  fof(f58,plain,(
% 0.22/0.48    ~v17_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | sK2 = k7_lattices(sK0,k7_lattices(sK0,sK2))),
% 0.22/0.48    inference(subsumption_resolution,[],[f49,f33])).
% 0.22/0.48  fof(f49,plain,(
% 0.22/0.48    ~v10_lattices(sK0) | ~v17_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | sK2 = k7_lattices(sK0,k7_lattices(sK0,sK2))),
% 0.22/0.48    inference(resolution,[],[f28,f37])).
% 0.22/0.48  fof(f37,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~v10_lattices(X0) | ~v17_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0) | k7_lattices(X0,k7_lattices(X0,X1)) = X1) )),
% 0.22/0.48    inference(cnf_transformation,[],[f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (k7_lattices(X0,k7_lattices(X0,X1)) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f19])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (k7_lattices(X0,k7_lattices(X0,X1)) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k7_lattices(X0,k7_lattices(X0,X1)) = X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_lattices)).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~r3_lattices(X0,X1,k7_lattices(X0,X2)) | ~v10_lattices(X0) | ~v17_lattices(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(X0) | k4_lattices(X0,X1,X2) = k5_lattices(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : ((k4_lattices(X0,X1,X2) = k5_lattices(X0) <=> r3_lattices(X0,X1,k7_lattices(X0,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : ((k4_lattices(X0,X1,X2) = k5_lattices(X0) <=> r3_lattices(X0,X1,k7_lattices(X0,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k4_lattices(X0,X1,X2) = k5_lattices(X0) <=> r3_lattices(X0,X1,k7_lattices(X0,X2))))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_lattices)).
% 0.22/0.48  fof(f135,plain,(
% 0.22/0.48    k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)) = k4_lattices(sK0,k7_lattices(sK0,sK2),sK1)),
% 0.22/0.48    inference(resolution,[],[f70,f63])).
% 0.22/0.48  fof(f70,plain,(
% 0.22/0.48    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k4_lattices(sK0,sK1,X0) = k4_lattices(sK0,X0,sK1)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f69,f32])).
% 0.22/0.48  fof(f69,plain,(
% 0.22/0.48    ( ! [X0] : (v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k4_lattices(sK0,sK1,X0) = k4_lattices(sK0,X0,sK1)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f68,f46])).
% 0.22/0.48  fof(f46,plain,(
% 0.22/0.48    l1_lattices(sK0)),
% 0.22/0.48    inference(resolution,[],[f35,f41])).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    ( ! [X0] : (~l3_lattices(X0) | l1_lattices(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f25])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,plain,(
% 0.22/0.48    ! [X0] : (l3_lattices(X0) => l1_lattices(X0))),
% 0.22/0.48    inference(pure_predicate_removal,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).
% 0.22/0.48  fof(f68,plain,(
% 0.22/0.48    ( ! [X0] : (~l1_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k4_lattices(sK0,sK1,X0) = k4_lattices(sK0,X0,sK1)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f64,f45])).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    v6_lattices(sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f44,f35])).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    ~l3_lattices(sK0) | v6_lattices(sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f43,f32])).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    v2_struct_0(sK0) | ~l3_lattices(sK0) | v6_lattices(sK0)),
% 0.22/0.48    inference(resolution,[],[f33,f42])).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    ( ! [X0] : (~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v6_lattices(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f27])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ! [X0] : ((v6_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 0.22/0.48    inference(flattening,[],[f26])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ! [X0] : (((v6_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v6_lattices(X0) & ~v2_struct_0(X0))))),
% 0.22/0.48    inference(pure_predicate_removal,[],[f13])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.22/0.48    inference(pure_predicate_removal,[],[f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.22/0.48    inference(pure_predicate_removal,[],[f11])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.22/0.48    inference(pure_predicate_removal,[],[f10])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.22/0.48    inference(pure_predicate_removal,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).
% 0.22/0.48  fof(f64,plain,(
% 0.22/0.48    ( ! [X0] : (~v6_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k4_lattices(sK0,sK1,X0) = k4_lattices(sK0,X0,sK1)) )),
% 0.22/0.48    inference(resolution,[],[f31,f40])).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~v6_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f24])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f23])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_lattices)).
% 0.22/0.48  fof(f166,plain,(
% 0.22/0.48    k5_lattices(sK0) != k4_lattices(sK0,k7_lattices(sK0,sK2),sK1)),
% 0.22/0.48    inference(subsumption_resolution,[],[f162,f30])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    ~r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))),
% 0.22/0.48    inference(cnf_transformation,[],[f16])).
% 0.22/0.48  fof(f162,plain,(
% 0.22/0.48    r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) | k5_lattices(sK0) != k4_lattices(sK0,k7_lattices(sK0,sK2),sK1)),
% 0.22/0.48    inference(resolution,[],[f91,f31])).
% 0.22/0.48  fof(f91,plain,(
% 0.22/0.48    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,X1)) | k5_lattices(sK0) != k4_lattices(sK0,k7_lattices(sK0,sK2),X1)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f90,f32])).
% 0.22/0.48  fof(f90,plain,(
% 0.22/0.48    ( ! [X1] : (v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,X1)) | k5_lattices(sK0) != k4_lattices(sK0,k7_lattices(sK0,sK2),X1)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f89,f35])).
% 0.22/0.48  fof(f89,plain,(
% 0.22/0.48    ( ! [X1] : (~l3_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,X1)) | k5_lattices(sK0) != k4_lattices(sK0,k7_lattices(sK0,sK2),X1)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f88,f34])).
% 0.22/0.48  fof(f88,plain,(
% 0.22/0.48    ( ! [X1] : (~v17_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,X1)) | k5_lattices(sK0) != k4_lattices(sK0,k7_lattices(sK0,sK2),X1)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f82,f33])).
% 0.22/0.48  fof(f82,plain,(
% 0.22/0.48    ( ! [X1] : (~v10_lattices(sK0) | ~v17_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,X1)) | k5_lattices(sK0) != k4_lattices(sK0,k7_lattices(sK0,sK2),X1)) )),
% 0.22/0.48    inference(resolution,[],[f63,f39])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~v10_lattices(X0) | ~v17_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | r3_lattices(X0,X1,k7_lattices(X0,X2)) | k4_lattices(X0,X1,X2) != k5_lattices(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f22])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (29837)------------------------------
% 0.22/0.48  % (29837)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (29837)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (29837)Memory used [KB]: 6140
% 0.22/0.48  % (29837)Time elapsed: 0.083 s
% 0.22/0.48  % (29837)------------------------------
% 0.22/0.48  % (29837)------------------------------
% 0.22/0.50  % (29818)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.50  % (29836)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.22/0.50  % (29839)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.22/0.50  % (29815)Success in time 0.142 s
%------------------------------------------------------------------------------
