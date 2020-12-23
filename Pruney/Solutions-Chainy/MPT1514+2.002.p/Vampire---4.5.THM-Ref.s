%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:46 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   74 (1991 expanded)
%              Number of leaves         :    8 ( 378 expanded)
%              Depth                    :   14
%              Number of atoms          :  380 (14480 expanded)
%              Number of equality atoms :   17 (  52 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f272,plain,(
    $false ),
    inference(subsumption_resolution,[],[f271,f191])).

fof(f191,plain,(
    r3_lattices(sK0,sK5(sK0,k15_lattice3(sK0,sK2),sK1),sK3(sK5(sK0,k15_lattice3(sK0,sK2),sK1))) ),
    inference(unit_resulting_resolution,[],[f177,f176,f30])).

fof(f30,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ r2_hidden(X3,sK1)
      | r3_lattices(sK0,X3,sK3(X3)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ~ r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
          & ! [X3] :
              ( ? [X4] :
                  ( r2_hidden(X4,X2)
                  & r3_lattices(X0,X3,X4)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_hidden(X3,X1)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ~ r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
          & ! [X3] :
              ( ? [X4] :
                  ( r2_hidden(X4,X2)
                  & r3_lattices(X0,X3,X4)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_hidden(X3,X1)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1,X2] :
            ( ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ~ ( ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ~ ( r2_hidden(X4,X2)
                            & r3_lattices(X0,X3,X4) ) )
                    & r2_hidden(X3,X1) ) )
           => r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X0))
             => ~ ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X0))
                     => ~ ( r2_hidden(X4,X2)
                          & r3_lattices(X0,X3,X4) ) )
                  & r2_hidden(X3,X1) ) )
         => r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_lattice3)).

fof(f176,plain,(
    m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK2),sK1),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f36,f33,f66,f113,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r4_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X3,X1)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X3,X1)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r4_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_hidden(X3,X2)
                   => r1_lattices(X0,X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_lattice3)).

fof(f113,plain,(
    ~ r4_lattice3(sK0,k15_lattice3(sK0,sK2),sK1) ),
    inference(unit_resulting_resolution,[],[f34,f36,f35,f33,f66,f85,f66,f61])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r4_lattice3(X0,X3,X1)
      | r1_lattices(X0,k15_lattice3(X0,X1),X3) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r4_lattice3(X0,X3,X1)
      | r1_lattices(X0,X2,X3)
      | k15_lattice3(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k15_lattice3(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_lattices(X0,X2,X3)
                  | ~ r4_lattice3(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r4_lattice3(X0,X2,X1) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k15_lattice3(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_lattices(X0,X2,X3)
                  | ~ r4_lattice3(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r4_lattice3(X0,X2,X1) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1,X2] :
            ( m1_subset_1(X2,u1_struct_0(X0))
           => ( k15_lattice3(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r4_lattice3(X0,X3,X1)
                     => r1_lattices(X0,X2,X3) ) )
                & r4_lattice3(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d21_lattice3)).

fof(f85,plain,(
    ~ r1_lattices(sK0,k15_lattice3(sK0,sK1),k15_lattice3(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f64,f63,f33,f65,f36,f66,f32,f66,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ v9_lattices(X0)
      | ~ v6_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_lattices(X0,X1,X2)
      | r3_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_lattices)).

fof(f32,plain,(
    ~ r3_lattices(sK0,k15_lattice3(sK0,sK1),k15_lattice3(sK0,sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f65,plain,(
    v9_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f36,f34,f33,f39])).

fof(f39,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
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

fof(f63,plain,(
    v6_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f36,f34,f33,f37])).

fof(f37,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f64,plain,(
    v8_lattices(sK0) ),
    inference(unit_resulting_resolution,[],[f36,f34,f33,f38])).

fof(f38,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f35,plain,(
    v4_lattice3(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f34,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f66,plain,(
    ! [X0] : m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f33,f36,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k15_lattice3)).

fof(f33,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f36,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f177,plain,(
    r2_hidden(sK5(sK0,k15_lattice3(sK0,sK2),sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f36,f33,f66,f113,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r2_hidden(sK5(X0,X1,X2),X2)
      | r4_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f271,plain,(
    ~ r3_lattices(sK0,sK5(sK0,k15_lattice3(sK0,sK2),sK1),sK3(sK5(sK0,k15_lattice3(sK0,sK2),sK1))) ),
    inference(unit_resulting_resolution,[],[f35,f34,f33,f36,f193,f192,f176,f260,f62])).

fof(f62,plain,(
    ! [X4,X2,X3,X1] :
      ( ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ r3_lattices(X1,X3,X4)
      | ~ r2_hidden(X4,X2)
      | r2_hidden(X3,a_2_5_lattice3(X1,X2)) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ l3_lattices(X1)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | X0 != X3
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ r3_lattices(X1,X3,X4)
      | ~ r2_hidden(X4,X2)
      | r2_hidden(X0,a_2_5_lattice3(X1,X2)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_5_lattice3(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r3_lattices(X1,X3,X4)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_5_lattice3(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r3_lattices(X1,X3,X4)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( l3_lattices(X1)
        & v4_lattice3(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_5_lattice3(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r3_lattices(X1,X3,X4)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_5_lattice3)).

fof(f260,plain,(
    ~ r2_hidden(sK5(sK0,k15_lattice3(sK0,sK2),sK1),a_2_5_lattice3(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f33,f36,f77,f66,f176,f175,f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X3,X2)
      | r1_lattices(X0,X3,X1)
      | ~ r4_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f175,plain,(
    ~ r1_lattices(sK0,sK5(sK0,k15_lattice3(sK0,sK2),sK1),k15_lattice3(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f36,f33,f66,f113,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r1_lattices(X0,sK5(X0,X1,X2),X1)
      | r4_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f77,plain,(
    ! [X0] : r4_lattice3(sK0,k15_lattice3(sK0,X0),a_2_5_lattice3(sK0,X0)) ),
    inference(subsumption_resolution,[],[f76,f33])).

fof(f76,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | r4_lattice3(sK0,k15_lattice3(sK0,X0),a_2_5_lattice3(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f75,f36])).

fof(f75,plain,(
    ! [X0] :
      ( ~ l3_lattices(sK0)
      | v2_struct_0(sK0)
      | r4_lattice3(sK0,k15_lattice3(sK0,X0),a_2_5_lattice3(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f74,f35])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v4_lattice3(sK0)
      | ~ l3_lattices(sK0)
      | v2_struct_0(sK0)
      | r4_lattice3(sK0,k15_lattice3(sK0,X0),a_2_5_lattice3(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f73,f34])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v10_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ l3_lattices(sK0)
      | v2_struct_0(sK0)
      | r4_lattice3(sK0,k15_lattice3(sK0,X0),a_2_5_lattice3(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f72,f66])).

fof(f72,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))
      | ~ v10_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ l3_lattices(sK0)
      | v2_struct_0(sK0)
      | r4_lattice3(sK0,k15_lattice3(sK0,X0),a_2_5_lattice3(sK0,X0)) ) ),
    inference(superposition,[],[f60,f67])).

fof(f67,plain,(
    ! [X0] : k15_lattice3(sK0,X0) = k15_lattice3(sK0,a_2_5_lattice3(sK0,X0)) ),
    inference(unit_resulting_resolution,[],[f35,f36,f33,f34,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1))
          & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1))
          & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1))
          & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_lattice3)).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | r4_lattice3(X0,k15_lattice3(X0,X1),X1) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r4_lattice3(X0,X2,X1)
      | k15_lattice3(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f192,plain,(
    m1_subset_1(sK3(sK5(sK0,k15_lattice3(sK0,sK2),sK1)),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f177,f176,f29])).

fof(f29,plain,(
    ! [X3] :
      ( m1_subset_1(sK3(X3),u1_struct_0(sK0))
      | ~ r2_hidden(X3,sK1)
      | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f193,plain,(
    r2_hidden(sK3(sK5(sK0,k15_lattice3(sK0,sK2),sK1)),sK2) ),
    inference(unit_resulting_resolution,[],[f177,f176,f31])).

fof(f31,plain,(
    ! [X3] :
      ( r2_hidden(sK3(X3),sK2)
      | ~ r2_hidden(X3,sK1)
      | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:44:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.54  % (17370)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.54  % (17355)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (17379)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.55  % (17365)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.55  % (17365)Refutation not found, incomplete strategy% (17365)------------------------------
% 0.21/0.55  % (17365)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (17365)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (17365)Memory used [KB]: 10618
% 0.21/0.55  % (17365)Time elapsed: 0.118 s
% 0.21/0.55  % (17365)------------------------------
% 0.21/0.55  % (17365)------------------------------
% 0.21/0.56  % (17354)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.56  % (17369)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.56  % (17354)Refutation not found, incomplete strategy% (17354)------------------------------
% 0.21/0.56  % (17354)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (17354)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (17354)Memory used [KB]: 10618
% 0.21/0.56  % (17354)Time elapsed: 0.116 s
% 0.21/0.56  % (17354)------------------------------
% 0.21/0.56  % (17354)------------------------------
% 0.21/0.56  % (17360)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.56  % (17356)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.56  % (17377)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.57  % (17357)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.57  % (17376)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.58  % (17361)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.58  % (17368)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.58  % (17364)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.59  % (17366)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.59  % (17359)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.60  % (17358)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.60  % (17361)Refutation found. Thanks to Tanya!
% 0.21/0.60  % SZS status Theorem for theBenchmark
% 0.21/0.60  % SZS output start Proof for theBenchmark
% 0.21/0.60  fof(f272,plain,(
% 0.21/0.60    $false),
% 0.21/0.60    inference(subsumption_resolution,[],[f271,f191])).
% 0.21/0.60  fof(f191,plain,(
% 0.21/0.60    r3_lattices(sK0,sK5(sK0,k15_lattice3(sK0,sK2),sK1),sK3(sK5(sK0,k15_lattice3(sK0,sK2),sK1)))),
% 0.21/0.60    inference(unit_resulting_resolution,[],[f177,f176,f30])).
% 0.21/0.60  fof(f30,plain,(
% 0.21/0.60    ( ! [X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | ~r2_hidden(X3,sK1) | r3_lattices(sK0,X3,sK3(X3))) )),
% 0.21/0.60    inference(cnf_transformation,[],[f14])).
% 0.21/0.60  fof(f14,plain,(
% 0.21/0.60    ? [X0] : (? [X1,X2] : (~r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) & ! [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.21/0.60    inference(flattening,[],[f13])).
% 0.21/0.60  fof(f13,plain,(
% 0.21/0.60    ? [X0] : (? [X1,X2] : (~r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) & ! [X3] : ((? [X4] : ((r2_hidden(X4,X2) & r3_lattices(X0,X3,X4)) & m1_subset_1(X4,u1_struct_0(X0))) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.21/0.60    inference(ennf_transformation,[],[f9])).
% 0.21/0.60  fof(f9,negated_conjecture,(
% 0.21/0.60    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(r2_hidden(X4,X2) & r3_lattices(X0,X3,X4))) & r2_hidden(X3,X1))) => r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))))),
% 0.21/0.60    inference(negated_conjecture,[],[f8])).
% 0.21/0.60  fof(f8,conjecture,(
% 0.21/0.60    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(r2_hidden(X4,X2) & r3_lattices(X0,X3,X4))) & r2_hidden(X3,X1))) => r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_lattice3)).
% 0.21/0.60  fof(f176,plain,(
% 0.21/0.60    m1_subset_1(sK5(sK0,k15_lattice3(sK0,sK2),sK1),u1_struct_0(sK0))),
% 0.21/0.60    inference(unit_resulting_resolution,[],[f36,f33,f66,f113,f48])).
% 0.21/0.60  fof(f48,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | r4_lattice3(X0,X1,X2)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f22])).
% 0.21/0.60  fof(f22,plain,(
% 0.21/0.60    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.60    inference(flattening,[],[f21])).
% 0.21/0.60  fof(f21,plain,(
% 0.21/0.60    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.60    inference(ennf_transformation,[],[f3])).
% 0.21/0.60  fof(f3,axiom,(
% 0.21/0.60    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X3,X1))))))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_lattice3)).
% 0.21/0.60  fof(f113,plain,(
% 0.21/0.60    ~r4_lattice3(sK0,k15_lattice3(sK0,sK2),sK1)),
% 0.21/0.60    inference(unit_resulting_resolution,[],[f34,f36,f35,f33,f66,f85,f66,f61])).
% 0.21/0.60  fof(f61,plain,(
% 0.21/0.60    ( ! [X0,X3,X1] : (~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~v10_lattices(X0) | ~v4_lattice3(X0) | ~l3_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r4_lattice3(X0,X3,X1) | r1_lattices(X0,k15_lattice3(X0,X1),X3)) )),
% 0.21/0.60    inference(equality_resolution,[],[f45])).
% 0.21/0.60  fof(f45,plain,(
% 0.21/0.60    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v10_lattices(X0) | ~v4_lattice3(X0) | ~l3_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r4_lattice3(X0,X3,X1) | r1_lattices(X0,X2,X3) | k15_lattice3(X0,X1) != X2) )),
% 0.21/0.60    inference(cnf_transformation,[],[f20])).
% 0.21/0.60  fof(f20,plain,(
% 0.21/0.60    ! [X0] : (! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.60    inference(flattening,[],[f19])).
% 0.21/0.60  fof(f19,plain,(
% 0.21/0.60    ! [X0] : ((! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : ((r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.60    inference(ennf_transformation,[],[f4])).
% 0.21/0.60  fof(f4,axiom,(
% 0.21/0.60    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k15_lattice3(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r4_lattice3(X0,X3,X1) => r1_lattices(X0,X2,X3))) & r4_lattice3(X0,X2,X1))))))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d21_lattice3)).
% 0.21/0.60  fof(f85,plain,(
% 0.21/0.60    ~r1_lattices(sK0,k15_lattice3(sK0,sK1),k15_lattice3(sK0,sK2))),
% 0.21/0.60    inference(unit_resulting_resolution,[],[f64,f63,f33,f65,f36,f66,f32,f66,f52])).
% 0.21/0.60  fof(f52,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (~v9_lattices(X0) | ~v6_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_lattices(X0,X1,X2) | r3_lattices(X0,X1,X2)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f26])).
% 0.21/0.60  fof(f26,plain,(
% 0.21/0.60    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.60    inference(flattening,[],[f25])).
% 0.21/0.60  fof(f25,plain,(
% 0.21/0.60    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.60    inference(ennf_transformation,[],[f2])).
% 0.21/0.60  fof(f2,axiom,(
% 0.21/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_lattices)).
% 0.21/0.60  fof(f32,plain,(
% 0.21/0.60    ~r3_lattices(sK0,k15_lattice3(sK0,sK1),k15_lattice3(sK0,sK2))),
% 0.21/0.60    inference(cnf_transformation,[],[f14])).
% 0.21/0.60  fof(f65,plain,(
% 0.21/0.60    v9_lattices(sK0)),
% 0.21/0.60    inference(unit_resulting_resolution,[],[f36,f34,f33,f39])).
% 0.21/0.60  fof(f39,plain,(
% 0.21/0.60    ( ! [X0] : (v9_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | ~l3_lattices(X0)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f16])).
% 0.21/0.60  fof(f16,plain,(
% 0.21/0.60    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 0.21/0.60    inference(flattening,[],[f15])).
% 0.21/0.60  fof(f15,plain,(
% 0.21/0.60    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 0.21/0.60    inference(ennf_transformation,[],[f12])).
% 0.21/0.60  fof(f12,plain,(
% 0.21/0.60    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.60    inference(pure_predicate_removal,[],[f11])).
% 0.21/0.60  fof(f11,plain,(
% 0.21/0.60    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.60    inference(pure_predicate_removal,[],[f10])).
% 0.21/0.60  fof(f10,plain,(
% 0.21/0.60    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.60    inference(pure_predicate_removal,[],[f1])).
% 0.21/0.60  fof(f1,axiom,(
% 0.21/0.60    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).
% 0.21/0.60  fof(f63,plain,(
% 0.21/0.60    v6_lattices(sK0)),
% 0.21/0.60    inference(unit_resulting_resolution,[],[f36,f34,f33,f37])).
% 0.21/0.60  fof(f37,plain,(
% 0.21/0.60    ( ! [X0] : (v6_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | ~l3_lattices(X0)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f16])).
% 0.21/0.60  fof(f64,plain,(
% 0.21/0.60    v8_lattices(sK0)),
% 0.21/0.60    inference(unit_resulting_resolution,[],[f36,f34,f33,f38])).
% 0.21/0.60  fof(f38,plain,(
% 0.21/0.60    ( ! [X0] : (v8_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | ~l3_lattices(X0)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f16])).
% 0.21/0.60  fof(f35,plain,(
% 0.21/0.60    v4_lattice3(sK0)),
% 0.21/0.60    inference(cnf_transformation,[],[f14])).
% 0.21/0.60  fof(f34,plain,(
% 0.21/0.60    v10_lattices(sK0)),
% 0.21/0.60    inference(cnf_transformation,[],[f14])).
% 0.21/0.60  fof(f66,plain,(
% 0.21/0.60    ( ! [X0] : (m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))) )),
% 0.21/0.60    inference(unit_resulting_resolution,[],[f33,f36,f51])).
% 0.21/0.60  fof(f51,plain,(
% 0.21/0.60    ( ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f24])).
% 0.21/0.60  fof(f24,plain,(
% 0.21/0.60    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.60    inference(flattening,[],[f23])).
% 0.21/0.60  fof(f23,plain,(
% 0.21/0.60    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.60    inference(ennf_transformation,[],[f5])).
% 0.21/0.60  fof(f5,axiom,(
% 0.21/0.60    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k15_lattice3)).
% 0.21/0.60  fof(f33,plain,(
% 0.21/0.60    ~v2_struct_0(sK0)),
% 0.21/0.60    inference(cnf_transformation,[],[f14])).
% 0.21/0.60  fof(f36,plain,(
% 0.21/0.60    l3_lattices(sK0)),
% 0.21/0.60    inference(cnf_transformation,[],[f14])).
% 0.21/0.60  fof(f177,plain,(
% 0.21/0.60    r2_hidden(sK5(sK0,k15_lattice3(sK0,sK2),sK1),sK1)),
% 0.21/0.60    inference(unit_resulting_resolution,[],[f36,f33,f66,f113,f49])).
% 0.21/0.60  fof(f49,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (~l3_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | r2_hidden(sK5(X0,X1,X2),X2) | r4_lattice3(X0,X1,X2)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f22])).
% 0.21/0.60  fof(f271,plain,(
% 0.21/0.60    ~r3_lattices(sK0,sK5(sK0,k15_lattice3(sK0,sK2),sK1),sK3(sK5(sK0,k15_lattice3(sK0,sK2),sK1)))),
% 0.21/0.60    inference(unit_resulting_resolution,[],[f35,f34,f33,f36,f193,f192,f176,f260,f62])).
% 0.21/0.60  fof(f62,plain,(
% 0.21/0.60    ( ! [X4,X2,X3,X1] : (~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X1) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~r3_lattices(X1,X3,X4) | ~r2_hidden(X4,X2) | r2_hidden(X3,a_2_5_lattice3(X1,X2))) )),
% 0.21/0.60    inference(equality_resolution,[],[f54])).
% 0.21/0.60  fof(f54,plain,(
% 0.21/0.60    ( ! [X4,X2,X0,X3,X1] : (v2_struct_0(X1) | ~v10_lattices(X1) | ~v4_lattice3(X1) | ~l3_lattices(X1) | ~m1_subset_1(X3,u1_struct_0(X1)) | X0 != X3 | ~m1_subset_1(X4,u1_struct_0(X1)) | ~r3_lattices(X1,X3,X4) | ~r2_hidden(X4,X2) | r2_hidden(X0,a_2_5_lattice3(X1,X2))) )),
% 0.21/0.60    inference(cnf_transformation,[],[f28])).
% 0.21/0.60  fof(f28,plain,(
% 0.21/0.60    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_5_lattice3(X1,X2)) <=> ? [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 0.21/0.60    inference(flattening,[],[f27])).
% 0.21/0.60  fof(f27,plain,(
% 0.21/0.60    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_5_lattice3(X1,X2)) <=> ? [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)))),
% 0.21/0.60    inference(ennf_transformation,[],[f6])).
% 0.21/0.60  fof(f6,axiom,(
% 0.21/0.60    ! [X0,X1,X2] : ((l3_lattices(X1) & v4_lattice3(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_5_lattice3(X1,X2)) <=> ? [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_5_lattice3)).
% 0.21/0.60  fof(f260,plain,(
% 0.21/0.60    ~r2_hidden(sK5(sK0,k15_lattice3(sK0,sK2),sK1),a_2_5_lattice3(sK0,sK2))),
% 0.21/0.60    inference(unit_resulting_resolution,[],[f33,f36,f77,f66,f176,f175,f47])).
% 0.21/0.60  fof(f47,plain,(
% 0.21/0.60    ( ! [X2,X0,X3,X1] : (~l3_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_hidden(X3,X2) | r1_lattices(X0,X3,X1) | ~r4_lattice3(X0,X1,X2)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f22])).
% 0.21/0.60  fof(f175,plain,(
% 0.21/0.60    ~r1_lattices(sK0,sK5(sK0,k15_lattice3(sK0,sK2),sK1),k15_lattice3(sK0,sK2))),
% 0.21/0.60    inference(unit_resulting_resolution,[],[f36,f33,f66,f113,f50])).
% 0.21/0.60  fof(f50,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (~l3_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r1_lattices(X0,sK5(X0,X1,X2),X1) | r4_lattice3(X0,X1,X2)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f22])).
% 0.21/0.60  fof(f77,plain,(
% 0.21/0.60    ( ! [X0] : (r4_lattice3(sK0,k15_lattice3(sK0,X0),a_2_5_lattice3(sK0,X0))) )),
% 0.21/0.60    inference(subsumption_resolution,[],[f76,f33])).
% 0.21/0.60  fof(f76,plain,(
% 0.21/0.60    ( ! [X0] : (v2_struct_0(sK0) | r4_lattice3(sK0,k15_lattice3(sK0,X0),a_2_5_lattice3(sK0,X0))) )),
% 0.21/0.60    inference(subsumption_resolution,[],[f75,f36])).
% 0.21/0.60  fof(f75,plain,(
% 0.21/0.60    ( ! [X0] : (~l3_lattices(sK0) | v2_struct_0(sK0) | r4_lattice3(sK0,k15_lattice3(sK0,X0),a_2_5_lattice3(sK0,X0))) )),
% 0.21/0.60    inference(subsumption_resolution,[],[f74,f35])).
% 0.21/0.60  fof(f74,plain,(
% 0.21/0.60    ( ! [X0] : (~v4_lattice3(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | r4_lattice3(sK0,k15_lattice3(sK0,X0),a_2_5_lattice3(sK0,X0))) )),
% 0.21/0.60    inference(subsumption_resolution,[],[f73,f34])).
% 0.21/0.60  fof(f73,plain,(
% 0.21/0.60    ( ! [X0] : (~v10_lattices(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | r4_lattice3(sK0,k15_lattice3(sK0,X0),a_2_5_lattice3(sK0,X0))) )),
% 0.21/0.60    inference(subsumption_resolution,[],[f72,f66])).
% 0.21/0.60  fof(f72,plain,(
% 0.21/0.60    ( ! [X0] : (~m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)) | ~v10_lattices(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | r4_lattice3(sK0,k15_lattice3(sK0,X0),a_2_5_lattice3(sK0,X0))) )),
% 0.21/0.60    inference(superposition,[],[f60,f67])).
% 0.21/0.60  fof(f67,plain,(
% 0.21/0.60    ( ! [X0] : (k15_lattice3(sK0,X0) = k15_lattice3(sK0,a_2_5_lattice3(sK0,X0))) )),
% 0.21/0.60    inference(unit_resulting_resolution,[],[f35,f36,f33,f34,f40])).
% 0.21/0.60  fof(f40,plain,(
% 0.21/0.60    ( ! [X0,X1] : (~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1))) )),
% 0.21/0.60    inference(cnf_transformation,[],[f18])).
% 0.21/0.60  fof(f18,plain,(
% 0.21/0.60    ! [X0] : (! [X1] : (k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1)) & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.60    inference(flattening,[],[f17])).
% 0.21/0.60  fof(f17,plain,(
% 0.21/0.60    ! [X0] : (! [X1] : (k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1)) & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.60    inference(ennf_transformation,[],[f7])).
% 0.21/0.60  fof(f7,axiom,(
% 0.21/0.60    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1)) & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1))))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_lattice3)).
% 0.21/0.60  fof(f60,plain,(
% 0.21/0.60    ( ! [X0,X1] : (~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~v10_lattices(X0) | ~v4_lattice3(X0) | ~l3_lattices(X0) | v2_struct_0(X0) | r4_lattice3(X0,k15_lattice3(X0,X1),X1)) )),
% 0.21/0.60    inference(equality_resolution,[],[f46])).
% 0.21/0.60  fof(f46,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v10_lattices(X0) | ~v4_lattice3(X0) | ~l3_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | r4_lattice3(X0,X2,X1) | k15_lattice3(X0,X1) != X2) )),
% 0.21/0.60    inference(cnf_transformation,[],[f20])).
% 0.21/0.60  fof(f192,plain,(
% 0.21/0.60    m1_subset_1(sK3(sK5(sK0,k15_lattice3(sK0,sK2),sK1)),u1_struct_0(sK0))),
% 0.21/0.60    inference(unit_resulting_resolution,[],[f177,f176,f29])).
% 0.21/0.61  fof(f29,plain,(
% 0.21/0.61    ( ! [X3] : (m1_subset_1(sK3(X3),u1_struct_0(sK0)) | ~r2_hidden(X3,sK1) | ~m1_subset_1(X3,u1_struct_0(sK0))) )),
% 0.21/0.61    inference(cnf_transformation,[],[f14])).
% 0.21/0.61  fof(f193,plain,(
% 0.21/0.61    r2_hidden(sK3(sK5(sK0,k15_lattice3(sK0,sK2),sK1)),sK2)),
% 0.21/0.61    inference(unit_resulting_resolution,[],[f177,f176,f31])).
% 0.21/0.61  fof(f31,plain,(
% 0.21/0.61    ( ! [X3] : (r2_hidden(sK3(X3),sK2) | ~r2_hidden(X3,sK1) | ~m1_subset_1(X3,u1_struct_0(sK0))) )),
% 0.21/0.61    inference(cnf_transformation,[],[f14])).
% 0.21/0.61  % SZS output end Proof for theBenchmark
% 0.21/0.61  % (17361)------------------------------
% 0.21/0.61  % (17361)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.61  % (17361)Termination reason: Refutation
% 0.21/0.61  
% 0.21/0.61  % (17361)Memory used [KB]: 1791
% 0.21/0.61  % (17361)Time elapsed: 0.104 s
% 0.21/0.61  % (17361)------------------------------
% 0.21/0.61  % (17361)------------------------------
% 0.21/0.61  % (17352)Success in time 0.239 s
%------------------------------------------------------------------------------
