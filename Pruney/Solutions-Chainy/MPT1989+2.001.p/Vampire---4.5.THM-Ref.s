%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:59 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 261 expanded)
%              Number of leaves         :   18 (  62 expanded)
%              Depth                    :   47
%              Number of atoms          : 1091 (2115 expanded)
%              Number of equality atoms :   31 (  51 expanded)
%              Maximal formula depth    :   22 (  10 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f684,plain,(
    $false ),
    inference(subsumption_resolution,[],[f683,f62])).

fof(f62,plain,(
    v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( ~ v4_waybel_7(sK1,sK0)
    & v5_waybel_6(sK1,sK0)
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v2_lattice3(sK0)
    & v1_lattice3(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f45,f44])).

fof(f44,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v4_waybel_7(X1,X0)
            & v5_waybel_6(X1,X0)
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ~ v4_waybel_7(X1,sK0)
          & v5_waybel_6(X1,sK0)
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v2_lattice3(sK0)
      & v1_lattice3(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X1] :
        ( ~ v4_waybel_7(X1,sK0)
        & v5_waybel_6(X1,sK0)
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ~ v4_waybel_7(sK1,sK0)
      & v5_waybel_6(sK1,sK0)
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v4_waybel_7(X1,X0)
          & v5_waybel_6(X1,X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v4_waybel_7(X1,X0)
          & v5_waybel_6(X1,X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v5_waybel_6(X1,X0)
             => v4_waybel_7(X1,X0) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v5_waybel_6(X1,X0)
           => v4_waybel_7(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_waybel_7)).

fof(f683,plain,(
    ~ v1_lattice3(sK0) ),
    inference(subsumption_resolution,[],[f682,f63])).

fof(f63,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f682,plain,
    ( ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0) ),
    inference(subsumption_resolution,[],[f681,f66])).

fof(f66,plain,(
    v5_waybel_6(sK1,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f681,plain,
    ( ~ v5_waybel_6(sK1,sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0) ),
    inference(subsumption_resolution,[],[f680,f61])).

fof(f61,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f680,plain,
    ( ~ v5_orders_2(sK0)
    | ~ v5_waybel_6(sK1,sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0) ),
    inference(subsumption_resolution,[],[f679,f67])).

fof(f67,plain,(
    ~ v4_waybel_7(sK1,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f679,plain,
    ( v4_waybel_7(sK1,sK0)
    | ~ v5_orders_2(sK0)
    | ~ v5_waybel_6(sK1,sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0) ),
    inference(subsumption_resolution,[],[f678,f64])).

fof(f64,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f678,plain,
    ( ~ l1_orders_2(sK0)
    | v4_waybel_7(sK1,sK0)
    | ~ v5_orders_2(sK0)
    | ~ v5_waybel_6(sK1,sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0) ),
    inference(subsumption_resolution,[],[f677,f59])).

fof(f59,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f677,plain,
    ( ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v4_waybel_7(sK1,sK0)
    | ~ v5_orders_2(sK0)
    | ~ v5_waybel_6(sK1,sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0) ),
    inference(subsumption_resolution,[],[f665,f60])).

fof(f60,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f665,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v4_waybel_7(sK1,sK0)
    | ~ v5_orders_2(sK0)
    | ~ v5_waybel_6(sK1,sK0)
    | ~ v2_lattice3(sK0)
    | ~ v1_lattice3(sK0) ),
    inference(resolution,[],[f663,f65])).

fof(f65,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f46])).

fof(f663,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v4_waybel_7(X1,X0)
      | ~ v5_orders_2(X0)
      | ~ v5_waybel_6(X1,X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0) ) ),
    inference(subsumption_resolution,[],[f662,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v1_lattice3(X0)
      | ~ v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).

fof(f662,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v4_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_waybel_6(X1,X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f653])).

fof(f653,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v4_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_waybel_6(X1,X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f650,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( r3_orders_2(X1,X0,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(condensation,[],[f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r3_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

fof(f650,plain,(
    ! [X2,X3] :
      ( ~ r3_orders_2(X2,X3,X3)
      | ~ v5_orders_2(X2)
      | ~ v4_orders_2(X2)
      | ~ v3_orders_2(X2)
      | ~ l1_orders_2(X2)
      | v4_waybel_7(X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ v5_waybel_6(X3,X2)
      | ~ v2_lattice3(X2)
      | ~ v1_lattice3(X2) ) ),
    inference(subsumption_resolution,[],[f647,f68])).

fof(f647,plain,(
    ! [X2,X3] :
      ( ~ v1_lattice3(X2)
      | ~ v5_orders_2(X2)
      | ~ v4_orders_2(X2)
      | ~ v3_orders_2(X2)
      | ~ l1_orders_2(X2)
      | v4_waybel_7(X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ v5_waybel_6(X3,X2)
      | ~ v2_lattice3(X2)
      | ~ r3_orders_2(X2,X3,X3)
      | v2_struct_0(X2) ) ),
    inference(duplicate_literal_removal,[],[f640])).

% (17679)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
fof(f640,plain,(
    ! [X2,X3] :
      ( ~ v1_lattice3(X2)
      | ~ v5_orders_2(X2)
      | ~ v4_orders_2(X2)
      | ~ v3_orders_2(X2)
      | ~ l1_orders_2(X2)
      | v4_waybel_7(X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ v5_waybel_6(X3,X2)
      | ~ v2_lattice3(X2)
      | ~ r3_orders_2(X2,X3,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_orders_2(X2)
      | ~ v3_orders_2(X2)
      | v2_struct_0(X2) ) ),
    inference(resolution,[],[f638,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_orders_2(X0,X1,X2)
          | ~ r1_orders_2(X0,X1,X2) )
        & ( r1_orders_2(X0,X1,X2)
          | ~ r3_orders_2(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f638,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(X0,X1,X1)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v4_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_waybel_6(X1,X0)
      | ~ v2_lattice3(X0) ) ),
    inference(subsumption_resolution,[],[f637,f68])).

fof(f637,plain,(
    ! [X0,X1] :
      ( ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v4_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_waybel_6(X1,X0)
      | ~ r1_orders_2(X0,X1,X1)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f636])).

fof(f636,plain,(
    ! [X0,X1] :
      ( ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v4_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_waybel_6(X1,X0)
      | ~ r1_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f635,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k5_waybel_0(X0,X1))
      | ~ r1_orders_2(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k5_waybel_0(X0,X1))
                  | ~ r1_orders_2(X0,X2,X1) )
                & ( r1_orders_2(X0,X2,X1)
                  | ~ r2_hidden(X2,k5_waybel_0(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k5_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X2,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k5_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X2,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k5_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_waybel_0)).

fof(f635,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k5_waybel_0(X0,X1))
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v4_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_waybel_6(X1,X0) ) ),
    inference(subsumption_resolution,[],[f634,f68])).

fof(f634,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ r2_hidden(X1,k5_waybel_0(X0,X1))
      | v4_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_waybel_6(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f633])).

fof(f633,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ r2_hidden(X1,k5_waybel_0(X0,X1))
      | v4_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_waybel_6(X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f632,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => v12_waybel_0(k5_waybel_0(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc12_waybel_0)).

fof(f632,plain,(
    ! [X0,X1] :
      ( ~ v12_waybel_0(k5_waybel_0(X1,X0),X1)
      | ~ l1_orders_2(X1)
      | ~ v2_lattice3(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | ~ r2_hidden(X0,k5_waybel_0(X1,X0))
      | v4_waybel_7(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ v5_waybel_6(X0,X1) ) ),
    inference(subsumption_resolution,[],[f631,f68])).

fof(f631,plain,(
    ! [X0,X1] :
      ( v4_waybel_7(X0,X1)
      | ~ l1_orders_2(X1)
      | ~ v2_lattice3(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | ~ r2_hidden(X0,k5_waybel_0(X1,X0))
      | ~ v12_waybel_0(k5_waybel_0(X1,X0),X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ v5_waybel_6(X0,X1)
      | v2_struct_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f630])).

fof(f630,plain,(
    ! [X0,X1] :
      ( v4_waybel_7(X0,X1)
      | ~ l1_orders_2(X1)
      | ~ v2_lattice3(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | ~ r2_hidden(X0,k5_waybel_0(X1,X0))
      | ~ v12_waybel_0(k5_waybel_0(X1,X0),X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ v5_waybel_6(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f629,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
        & ~ v1_xboole_0(k5_waybel_0(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
        & ~ v1_xboole_0(k5_waybel_0(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
        & ~ v1_xboole_0(k5_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_waybel_0)).

fof(f629,plain,(
    ! [X0,X1] :
      ( ~ v1_waybel_0(k5_waybel_0(X0,X1),X0)
      | v4_waybel_7(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ r2_hidden(X1,k5_waybel_0(X0,X1))
      | ~ v12_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_waybel_6(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f628])).

fof(f628,plain,(
    ! [X0,X1] :
      ( ~ v1_waybel_0(k5_waybel_0(X0,X1),X0)
      | v4_waybel_7(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ r2_hidden(X1,k5_waybel_0(X0,X1))
      | ~ v12_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_waybel_6(X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(resolution,[],[f626,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( v1_waybel_7(k5_waybel_0(X0,X1),X0)
      | ~ v5_waybel_6(X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_waybel_7(k5_waybel_0(X0,X1),X0)
          | ~ v5_waybel_6(X1,X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_waybel_7(k5_waybel_0(X0,X1),X0)
          | ~ v5_waybel_6(X1,X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v5_waybel_6(X1,X0)
           => v1_waybel_7(k5_waybel_0(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_waybel_7)).

fof(f626,plain,(
    ! [X0,X1] :
      ( ~ v1_waybel_7(k5_waybel_0(X0,X1),X0)
      | ~ v1_waybel_0(k5_waybel_0(X0,X1),X0)
      | v4_waybel_7(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ r2_hidden(X1,k5_waybel_0(X0,X1))
      | ~ v12_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f625,f68])).

fof(f625,plain,(
    ! [X0,X1] :
      ( ~ v12_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ v1_waybel_0(k5_waybel_0(X0,X1),X0)
      | v4_waybel_7(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ r2_hidden(X1,k5_waybel_0(X0,X1))
      | ~ v1_waybel_7(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f618])).

fof(f618,plain,(
    ! [X0,X1] :
      ( ~ v12_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ v1_waybel_0(k5_waybel_0(X0,X1),X0)
      | v4_waybel_7(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ r2_hidden(X1,k5_waybel_0(X0,X1))
      | ~ v1_waybel_7(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0)) ) ),
    inference(resolution,[],[f508,f190])).

fof(f190,plain,(
    ! [X0,X1] :
      ( r2_lattice3(X1,k5_waybel_0(X1,X0),X0)
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f187])).

fof(f187,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | r2_lattice3(X1,k5_waybel_0(X1,X0),X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | r2_lattice3(X1,k5_waybel_0(X1,X0),X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1) ) ),
    inference(resolution,[],[f116,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK2(X0,X1,X2),X2)
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,sK2(X0,X1,X2),X2)
                & r2_hidden(sK2(X0,X1,X2),X1)
                & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f48,f49])).

fof(f49,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK2(X0,X1,X2),X2)
        & r2_hidden(sK2(X0,X1,X2),X1)
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).

fof(f116,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,sK2(X1,k5_waybel_0(X0,X2),X3),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | r2_lattice3(X1,k5_waybel_0(X0,X2),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_orders_2(X1) ) ),
    inference(subsumption_resolution,[],[f115,f107])).

fof(f107,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK2(X1,k5_waybel_0(X0,X2),X3),u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_lattice3(X1,k5_waybel_0(X0,X2),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_orders_2(X1) ) ),
    inference(resolution,[],[f106,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X1)
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k5_waybel_0(X1,X0))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(resolution,[],[f95,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f95,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_waybel_0)).

fof(f115,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,sK2(X1,k5_waybel_0(X0,X2),X3),X2)
      | ~ m1_subset_1(sK2(X1,k5_waybel_0(X0,X2),X3),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | r2_lattice3(X1,k5_waybel_0(X0,X2),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_orders_2(X1) ) ),
    inference(resolution,[],[f73,f71])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k5_waybel_0(X0,X1))
      | r1_orders_2(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

% (17663)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
fof(f508,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_lattice3(X0,k5_waybel_0(X0,X1),X2)
      | ~ v12_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ v1_waybel_0(k5_waybel_0(X0,X1),X0)
      | v4_waybel_7(X2,X0)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ r2_hidden(X2,k5_waybel_0(X0,X1))
      | ~ v1_waybel_7(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f507,f68])).

fof(f507,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_waybel_7(k5_waybel_0(X0,X1),X0)
      | ~ v12_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ v1_waybel_0(k5_waybel_0(X0,X1),X0)
      | v4_waybel_7(X2,X0)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ r2_hidden(X2,k5_waybel_0(X0,X1))
      | ~ r2_lattice3(X0,k5_waybel_0(X0,X1),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f506,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k5_waybel_0(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f506,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_waybel_7(k5_waybel_0(X0,X1),X0)
      | ~ v12_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ v1_waybel_0(k5_waybel_0(X0,X1),X0)
      | v1_xboole_0(k5_waybel_0(X0,X1))
      | v4_waybel_7(X2,X0)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ r2_hidden(X2,k5_waybel_0(X0,X1))
      | ~ r2_lattice3(X0,k5_waybel_0(X0,X1),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f503])).

fof(f503,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_waybel_7(k5_waybel_0(X0,X1),X0)
      | ~ v12_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ v1_waybel_0(k5_waybel_0(X0,X1),X0)
      | v1_xboole_0(k5_waybel_0(X0,X1))
      | v4_waybel_7(X2,X0)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ r2_hidden(X2,k5_waybel_0(X0,X1))
      | ~ r2_lattice3(X0,k5_waybel_0(X0,X1),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f299,f95])).

fof(f299,plain,(
    ! [X12,X10,X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
      | ~ v1_waybel_7(X11,X10)
      | ~ v12_waybel_0(X11,X10)
      | ~ v1_waybel_0(X11,X10)
      | v1_xboole_0(X11)
      | v4_waybel_7(X12,X10)
      | ~ l1_orders_2(X10)
      | ~ v2_lattice3(X10)
      | ~ v1_lattice3(X10)
      | ~ v5_orders_2(X10)
      | ~ v4_orders_2(X10)
      | ~ v3_orders_2(X10)
      | ~ r2_hidden(X12,X11)
      | ~ r2_lattice3(X10,X11,X12) ) ),
    inference(subsumption_resolution,[],[f291,f99])).

fof(f291,plain,(
    ! [X12,X10,X11] :
      ( ~ m1_subset_1(X12,u1_struct_0(X10))
      | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
      | ~ v1_waybel_7(X11,X10)
      | ~ v12_waybel_0(X11,X10)
      | ~ v1_waybel_0(X11,X10)
      | v1_xboole_0(X11)
      | v4_waybel_7(X12,X10)
      | ~ l1_orders_2(X10)
      | ~ v2_lattice3(X10)
      | ~ v1_lattice3(X10)
      | ~ v5_orders_2(X10)
      | ~ v4_orders_2(X10)
      | ~ v3_orders_2(X10)
      | ~ r2_hidden(X12,X11)
      | ~ r2_lattice3(X10,X11,X12) ) ),
    inference(duplicate_literal_removal,[],[f274])).

fof(f274,plain,(
    ! [X12,X10,X11] :
      ( ~ m1_subset_1(X12,u1_struct_0(X10))
      | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
      | ~ v1_waybel_7(X11,X10)
      | ~ v12_waybel_0(X11,X10)
      | ~ v1_waybel_0(X11,X10)
      | v1_xboole_0(X11)
      | v4_waybel_7(X12,X10)
      | ~ l1_orders_2(X10)
      | ~ v2_lattice3(X10)
      | ~ v1_lattice3(X10)
      | ~ v5_orders_2(X10)
      | ~ v4_orders_2(X10)
      | ~ v3_orders_2(X10)
      | ~ m1_subset_1(X12,u1_struct_0(X10))
      | ~ l1_orders_2(X10)
      | ~ v5_orders_2(X10)
      | ~ r2_hidden(X12,X11)
      | ~ r2_lattice3(X10,X11,X12) ) ),
    inference(superposition,[],[f102,f263])).

fof(f263,plain,(
    ! [X6,X4,X5] :
      ( k1_yellow_0(X4,X5) = X6
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v5_orders_2(X4)
      | ~ r2_hidden(X6,X5)
      | ~ r2_lattice3(X4,X5,X6) ) ),
    inference(duplicate_literal_removal,[],[f258])).

fof(f258,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_lattice3(X4,X5,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v5_orders_2(X4)
      | ~ r2_hidden(X6,X5)
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | k1_yellow_0(X4,X5) = X6
      | k1_yellow_0(X4,X5) = X6
      | ~ r2_lattice3(X4,X5,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v5_orders_2(X4) ) ),
    inference(resolution,[],[f140,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,sK3(X0,X1,X2))
      | k1_yellow_0(X0,X2) = X1
      | ~ r2_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | ( ~ r1_orders_2(X0,X1,sK3(X0,X1,X2))
                  & r2_lattice3(X0,X2,sK3(X0,X1,X2))
                  & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X1,X4)
                      | ~ r2_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | ~ r1_yellow_0(X0,X2)
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f52])).

fof(f52,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X1,X3)
          & r2_lattice3(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X1,sK3(X0,X1,X2))
        & r2_lattice3(X0,X2,sK3(X0,X1,X2))
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X1,X3)
                    & r2_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X1,X4)
                      | ~ r2_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | ~ r1_yellow_0(X0,X2)
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X1,X3)
                    & r2_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X1,X4)
                      | ~ r2_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | ~ r1_yellow_0(X0,X2)
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
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
               => ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X4)
                       => r1_orders_2(X0,X1,X4) ) )
                  & r2_lattice3(X0,X2,X1) ) ) ) ) ) ),
    inference(rectify,[],[f7])).

% (17659)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
fof(f7,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_yellow_0)).

fof(f140,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,sK3(X0,X2,X1))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k1_yellow_0(X0,X1) = X2 ) ),
    inference(subsumption_resolution,[],[f139,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | k1_yellow_0(X0,X2) = X1
      | ~ r2_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f139,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_yellow_0(X0,X1) = X2
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_orders_2(X0,X3,sK3(X0,X2,X1))
      | ~ m1_subset_1(sK3(X0,X2,X1),u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f138])).

fof(f138,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_yellow_0(X0,X1) = X2
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_orders_2(X0,X3,sK3(X0,X2,X1))
      | ~ m1_subset_1(sK3(X0,X2,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f78,f69])).

fof(f69,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_lattice3(X0,X1,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_orders_2(X0,X4,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X2,sK3(X0,X1,X2))
      | k1_yellow_0(X0,X2) = X1
      | ~ r2_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f102,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(k1_yellow_0(X0,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_waybel_7(X2,X0)
      | ~ v12_waybel_0(X2,X0)
      | ~ v1_waybel_0(X2,X0)
      | v1_xboole_0(X2)
      | v4_waybel_7(k1_yellow_0(X0,X2),X0)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( v4_waybel_7(X1,X0)
      | k1_yellow_0(X0,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_waybel_7(X2,X0)
      | ~ v12_waybel_0(X2,X0)
      | ~ v1_waybel_0(X2,X0)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_waybel_7(X1,X0)
              | ! [X2] :
                  ( k1_yellow_0(X0,X2) != X1
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ v1_waybel_7(X2,X0)
                  | ~ v12_waybel_0(X2,X0)
                  | ~ v1_waybel_0(X2,X0)
                  | v1_xboole_0(X2) ) )
            & ( ( k1_yellow_0(X0,sK4(X0,X1)) = X1
                & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
                & v1_waybel_7(sK4(X0,X1),X0)
                & v12_waybel_0(sK4(X0,X1),X0)
                & v1_waybel_0(sK4(X0,X1),X0)
                & ~ v1_xboole_0(sK4(X0,X1)) )
              | ~ v4_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f55,f56])).

fof(f56,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( k1_yellow_0(X0,X3) = X1
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_waybel_7(X3,X0)
          & v12_waybel_0(X3,X0)
          & v1_waybel_0(X3,X0)
          & ~ v1_xboole_0(X3) )
     => ( k1_yellow_0(X0,sK4(X0,X1)) = X1
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        & v1_waybel_7(sK4(X0,X1),X0)
        & v12_waybel_0(sK4(X0,X1),X0)
        & v1_waybel_0(sK4(X0,X1),X0)
        & ~ v1_xboole_0(sK4(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_waybel_7(X1,X0)
              | ! [X2] :
                  ( k1_yellow_0(X0,X2) != X1
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ v1_waybel_7(X2,X0)
                  | ~ v12_waybel_0(X2,X0)
                  | ~ v1_waybel_0(X2,X0)
                  | v1_xboole_0(X2) ) )
            & ( ? [X3] :
                  ( k1_yellow_0(X0,X3) = X1
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  & v1_waybel_7(X3,X0)
                  & v12_waybel_0(X3,X0)
                  & v1_waybel_0(X3,X0)
                  & ~ v1_xboole_0(X3) )
              | ~ v4_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(rectify,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_waybel_7(X1,X0)
              | ! [X2] :
                  ( k1_yellow_0(X0,X2) != X1
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ v1_waybel_7(X2,X0)
                  | ~ v12_waybel_0(X2,X0)
                  | ~ v1_waybel_0(X2,X0)
                  | v1_xboole_0(X2) ) )
            & ( ? [X2] :
                  ( k1_yellow_0(X0,X2) = X1
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  & v1_waybel_7(X2,X0)
                  & v12_waybel_0(X2,X0)
                  & v1_waybel_0(X2,X0)
                  & ~ v1_xboole_0(X2) )
              | ~ v4_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_waybel_7(X1,X0)
          <=> ? [X2] :
                ( k1_yellow_0(X0,X2) = X1
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & v1_waybel_7(X2,X0)
                & v12_waybel_0(X2,X0)
                & v1_waybel_0(X2,X0)
                & ~ v1_xboole_0(X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_waybel_7(X1,X0)
          <=> ? [X2] :
                ( k1_yellow_0(X0,X2) = X1
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & v1_waybel_7(X2,X0)
                & v12_waybel_0(X2,X0)
                & v1_waybel_0(X2,X0)
                & ~ v1_xboole_0(X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v4_waybel_7(X1,X0)
          <=> ? [X2] :
                ( k1_yellow_0(X0,X2) = X1
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & v1_waybel_7(X2,X0)
                & v12_waybel_0(X2,X0)
                & v1_waybel_0(X2,X0)
                & ~ v1_xboole_0(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_waybel_7)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:35:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (17669)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.47  % (17678)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.47  % (17660)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % (17664)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.47  % (17660)Refutation not found, incomplete strategy% (17660)------------------------------
% 0.21/0.47  % (17660)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (17666)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.48  % (17660)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (17660)Memory used [KB]: 10618
% 0.21/0.48  % (17660)Time elapsed: 0.070 s
% 0.21/0.48  % (17660)------------------------------
% 0.21/0.48  % (17660)------------------------------
% 0.21/0.48  % (17662)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.48  % (17677)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.49  % (17668)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  % (17674)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (17675)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.49  % (17676)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.49  % (17667)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.49  % (17672)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.50  % (17670)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.50  % (17671)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (17661)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.50  % (17678)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % (17665)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f684,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(subsumption_resolution,[],[f683,f62])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    v1_lattice3(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f46])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    (~v4_waybel_7(sK1,sK0) & v5_waybel_6(sK1,sK0) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v2_lattice3(sK0) & v1_lattice3(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f45,f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (~v4_waybel_7(X1,X0) & v5_waybel_6(X1,X0) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => (? [X1] : (~v4_waybel_7(X1,sK0) & v5_waybel_6(X1,sK0) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v2_lattice3(sK0) & v1_lattice3(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ? [X1] : (~v4_waybel_7(X1,sK0) & v5_waybel_6(X1,sK0) & m1_subset_1(X1,u1_struct_0(sK0))) => (~v4_waybel_7(sK1,sK0) & v5_waybel_6(sK1,sK0) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (~v4_waybel_7(X1,X0) & v5_waybel_6(X1,X0) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0))),
% 0.21/0.50    inference(flattening,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : ((~v4_waybel_7(X1,X0) & v5_waybel_6(X1,X0)) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,negated_conjecture,(
% 0.21/0.50    ~! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v5_waybel_6(X1,X0) => v4_waybel_7(X1,X0))))),
% 0.21/0.50    inference(negated_conjecture,[],[f14])).
% 0.21/0.50  fof(f14,conjecture,(
% 0.21/0.50    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v5_waybel_6(X1,X0) => v4_waybel_7(X1,X0))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_waybel_7)).
% 0.21/0.50  fof(f683,plain,(
% 0.21/0.50    ~v1_lattice3(sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f682,f63])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    v2_lattice3(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f46])).
% 0.21/0.50  fof(f682,plain,(
% 0.21/0.50    ~v2_lattice3(sK0) | ~v1_lattice3(sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f681,f66])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    v5_waybel_6(sK1,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f46])).
% 0.21/0.50  fof(f681,plain,(
% 0.21/0.50    ~v5_waybel_6(sK1,sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f680,f61])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    v5_orders_2(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f46])).
% 0.21/0.50  fof(f680,plain,(
% 0.21/0.50    ~v5_orders_2(sK0) | ~v5_waybel_6(sK1,sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f679,f67])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    ~v4_waybel_7(sK1,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f46])).
% 0.21/0.50  fof(f679,plain,(
% 0.21/0.50    v4_waybel_7(sK1,sK0) | ~v5_orders_2(sK0) | ~v5_waybel_6(sK1,sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f678,f64])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    l1_orders_2(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f46])).
% 0.21/0.50  fof(f678,plain,(
% 0.21/0.50    ~l1_orders_2(sK0) | v4_waybel_7(sK1,sK0) | ~v5_orders_2(sK0) | ~v5_waybel_6(sK1,sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f677,f59])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    v3_orders_2(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f46])).
% 0.21/0.50  fof(f677,plain,(
% 0.21/0.50    ~v3_orders_2(sK0) | ~l1_orders_2(sK0) | v4_waybel_7(sK1,sK0) | ~v5_orders_2(sK0) | ~v5_waybel_6(sK1,sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f665,f60])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    v4_orders_2(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f46])).
% 0.21/0.50  fof(f665,plain,(
% 0.21/0.50    ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~l1_orders_2(sK0) | v4_waybel_7(sK1,sK0) | ~v5_orders_2(sK0) | ~v5_waybel_6(sK1,sK0) | ~v2_lattice3(sK0) | ~v1_lattice3(sK0)),
% 0.21/0.50    inference(resolution,[],[f663,f65])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.50    inference(cnf_transformation,[],[f46])).
% 0.21/0.50  fof(f663,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | v4_waybel_7(X1,X0) | ~v5_orders_2(X0) | ~v5_waybel_6(X1,X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f662,f68])).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_lattice3(X0) | ~v2_struct_0(X0) | ~l1_orders_2(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 0.21/0.50    inference(flattening,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).
% 0.21/0.50  fof(f662,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | v4_waybel_7(X1,X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v5_waybel_6(X1,X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f653])).
% 0.21/0.50  fof(f653,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | v4_waybel_7(X1,X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v5_waybel_6(X1,X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(resolution,[],[f650,f103])).
% 0.21/0.50  fof(f103,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r3_orders_2(X1,X0,X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 0.21/0.50    inference(condensation,[],[f96])).
% 0.21/0.50  fof(f96,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r3_orders_2(X0,X1,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (r3_orders_2(X0,X1,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (r3_orders_2(X0,X1,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => r3_orders_2(X0,X1,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).
% 0.21/0.50  fof(f650,plain,(
% 0.21/0.50    ( ! [X2,X3] : (~r3_orders_2(X2,X3,X3) | ~v5_orders_2(X2) | ~v4_orders_2(X2) | ~v3_orders_2(X2) | ~l1_orders_2(X2) | v4_waybel_7(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~v5_waybel_6(X3,X2) | ~v2_lattice3(X2) | ~v1_lattice3(X2)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f647,f68])).
% 0.21/0.50  fof(f647,plain,(
% 0.21/0.50    ( ! [X2,X3] : (~v1_lattice3(X2) | ~v5_orders_2(X2) | ~v4_orders_2(X2) | ~v3_orders_2(X2) | ~l1_orders_2(X2) | v4_waybel_7(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~v5_waybel_6(X3,X2) | ~v2_lattice3(X2) | ~r3_orders_2(X2,X3,X3) | v2_struct_0(X2)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f640])).
% 0.21/0.50  % (17679)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.50  fof(f640,plain,(
% 0.21/0.50    ( ! [X2,X3] : (~v1_lattice3(X2) | ~v5_orders_2(X2) | ~v4_orders_2(X2) | ~v3_orders_2(X2) | ~l1_orders_2(X2) | v4_waybel_7(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~v5_waybel_6(X3,X2) | ~v2_lattice3(X2) | ~r3_orders_2(X2,X3,X3) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_orders_2(X2) | ~v3_orders_2(X2) | v2_struct_0(X2)) )),
% 0.21/0.50    inference(resolution,[],[f638,f97])).
% 0.21/0.50  fof(f97,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f58])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).
% 0.21/0.50  fof(f638,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_orders_2(X0,X1,X1) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | v4_waybel_7(X1,X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v5_waybel_6(X1,X0) | ~v2_lattice3(X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f637,f68])).
% 0.21/0.50  fof(f637,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | v4_waybel_7(X1,X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v5_waybel_6(X1,X0) | ~r1_orders_2(X0,X1,X1) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f636])).
% 0.21/0.50  fof(f636,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | v4_waybel_7(X1,X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v5_waybel_6(X1,X0) | ~r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(resolution,[],[f635,f74])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r2_hidden(X2,k5_waybel_0(X0,X1)) | ~r1_orders_2(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f51])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k5_waybel_0(X0,X1)) | ~r1_orders_2(X0,X2,X1)) & (r1_orders_2(X0,X2,X1) | ~r2_hidden(X2,k5_waybel_0(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k5_waybel_0(X0,X1)) <=> r1_orders_2(X0,X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k5_waybel_0(X0,X1)) <=> r1_orders_2(X0,X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,axiom,(
% 0.21/0.50    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k5_waybel_0(X0,X1)) <=> r1_orders_2(X0,X2,X1)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_waybel_0)).
% 0.21/0.50  fof(f635,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(X1,k5_waybel_0(X0,X1)) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | v4_waybel_7(X1,X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v5_waybel_6(X1,X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f634,f68])).
% 0.21/0.50  fof(f634,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~r2_hidden(X1,k5_waybel_0(X0,X1)) | v4_waybel_7(X1,X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v5_waybel_6(X1,X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f633])).
% 0.21/0.50  fof(f633,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~r2_hidden(X1,k5_waybel_0(X0,X1)) | v4_waybel_7(X1,X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v5_waybel_6(X1,X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(resolution,[],[f632,f92])).
% 0.21/0.50  fof(f92,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v12_waybel_0(k5_waybel_0(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ! [X0,X1] : (v12_waybel_0(k5_waybel_0(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ! [X0,X1] : (v12_waybel_0(k5_waybel_0(X0,X1),X0) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v4_orders_2(X0) & ~v2_struct_0(X0)) => v12_waybel_0(k5_waybel_0(X0,X1),X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc12_waybel_0)).
% 0.21/0.50  fof(f632,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v12_waybel_0(k5_waybel_0(X1,X0),X1) | ~l1_orders_2(X1) | ~v2_lattice3(X1) | ~v1_lattice3(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | ~r2_hidden(X0,k5_waybel_0(X1,X0)) | v4_waybel_7(X0,X1) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~v5_waybel_6(X0,X1)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f631,f68])).
% 0.21/0.50  fof(f631,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v4_waybel_7(X0,X1) | ~l1_orders_2(X1) | ~v2_lattice3(X1) | ~v1_lattice3(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | ~r2_hidden(X0,k5_waybel_0(X1,X0)) | ~v12_waybel_0(k5_waybel_0(X1,X0),X1) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~v5_waybel_6(X0,X1) | v2_struct_0(X1)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f630])).
% 0.21/0.50  fof(f630,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v4_waybel_7(X0,X1) | ~l1_orders_2(X1) | ~v2_lattice3(X1) | ~v1_lattice3(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | ~r2_hidden(X0,k5_waybel_0(X1,X0)) | ~v12_waybel_0(k5_waybel_0(X1,X0),X1) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~v5_waybel_6(X0,X1) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 0.21/0.50    inference(resolution,[],[f629,f94])).
% 0.21/0.50  fof(f94,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v1_waybel_0(k5_waybel_0(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ! [X0,X1] : ((v1_waybel_0(k5_waybel_0(X0,X1),X0) & ~v1_xboole_0(k5_waybel_0(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ! [X0,X1] : ((v1_waybel_0(k5_waybel_0(X0,X1),X0) & ~v1_xboole_0(k5_waybel_0(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (v1_waybel_0(k5_waybel_0(X0,X1),X0) & ~v1_xboole_0(k5_waybel_0(X0,X1))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_waybel_0)).
% 0.21/0.50  fof(f629,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_waybel_0(k5_waybel_0(X0,X1),X0) | v4_waybel_7(X1,X0) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~r2_hidden(X1,k5_waybel_0(X0,X1)) | ~v12_waybel_0(k5_waybel_0(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v5_waybel_6(X1,X0)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f628])).
% 0.21/0.50  fof(f628,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_waybel_0(k5_waybel_0(X0,X1),X0) | v4_waybel_7(X1,X0) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~r2_hidden(X1,k5_waybel_0(X0,X1)) | ~v12_waybel_0(k5_waybel_0(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v5_waybel_6(X1,X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0)) )),
% 0.21/0.50    inference(resolution,[],[f626,f83])).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v1_waybel_7(k5_waybel_0(X0,X1),X0) | ~v5_waybel_6(X1,X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (v1_waybel_7(k5_waybel_0(X0,X1),X0) | ~v5_waybel_6(X1,X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0))),
% 0.21/0.50    inference(flattening,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((v1_waybel_7(k5_waybel_0(X0,X1),X0) | ~v5_waybel_6(X1,X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,axiom,(
% 0.21/0.50    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v5_waybel_6(X1,X0) => v1_waybel_7(k5_waybel_0(X0,X1),X0))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_waybel_7)).
% 0.21/0.50  fof(f626,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_waybel_7(k5_waybel_0(X0,X1),X0) | ~v1_waybel_0(k5_waybel_0(X0,X1),X0) | v4_waybel_7(X1,X0) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~r2_hidden(X1,k5_waybel_0(X0,X1)) | ~v12_waybel_0(k5_waybel_0(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f625,f68])).
% 0.21/0.50  fof(f625,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v12_waybel_0(k5_waybel_0(X0,X1),X0) | ~v1_waybel_0(k5_waybel_0(X0,X1),X0) | v4_waybel_7(X1,X0) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~r2_hidden(X1,k5_waybel_0(X0,X1)) | ~v1_waybel_7(k5_waybel_0(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f618])).
% 0.21/0.50  fof(f618,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v12_waybel_0(k5_waybel_0(X0,X1),X0) | ~v1_waybel_0(k5_waybel_0(X0,X1),X0) | v4_waybel_7(X1,X0) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~r2_hidden(X1,k5_waybel_0(X0,X1)) | ~v1_waybel_7(k5_waybel_0(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0))) )),
% 0.21/0.50    inference(resolution,[],[f508,f190])).
% 0.21/0.50  fof(f190,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r2_lattice3(X1,k5_waybel_0(X1,X0),X0) | ~l1_orders_2(X1) | v2_struct_0(X1) | ~m1_subset_1(X0,u1_struct_0(X1))) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f187])).
% 0.21/0.50  fof(f187,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_orders_2(X1) | v2_struct_0(X1) | r2_lattice3(X1,k5_waybel_0(X1,X0),X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_orders_2(X1) | r2_lattice3(X1,k5_waybel_0(X1,X0),X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_orders_2(X1)) )),
% 0.21/0.50    inference(resolution,[],[f116,f72])).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r1_orders_2(X0,sK2(X0,X1,X2),X2) | r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f50])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | (~r1_orders_2(X0,sK2(X0,X1,X2),X2) & r2_hidden(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f48,f49])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK2(X0,X1,X2),X2) & r2_hidden(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.50    inference(rectify,[],[f47])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.50    inference(flattening,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).
% 0.21/0.50  fof(f116,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,sK2(X1,k5_waybel_0(X0,X2),X3),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0) | r2_lattice3(X1,k5_waybel_0(X0,X2),X3) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l1_orders_2(X1)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f115,f107])).
% 0.21/0.50  fof(f107,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK2(X1,k5_waybel_0(X0,X2),X3),u1_struct_0(X0)) | v2_struct_0(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_lattice3(X1,k5_waybel_0(X0,X2),X3) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l1_orders_2(X1)) )),
% 0.21/0.50    inference(resolution,[],[f106,f71])).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X1) | r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f50])).
% 0.21/0.50  fof(f106,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X2,k5_waybel_0(X1,X0)) | ~l1_orders_2(X1) | v2_struct_0(X1) | m1_subset_1(X2,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(X1))) )),
% 0.21/0.50    inference(resolution,[],[f95,f99])).
% 0.21/0.50  fof(f99,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.50    inference(flattening,[],[f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.21/0.50  fof(f95,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_waybel_0)).
% 0.21/0.50  fof(f115,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,sK2(X1,k5_waybel_0(X0,X2),X3),X2) | ~m1_subset_1(sK2(X1,k5_waybel_0(X0,X2),X3),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0) | r2_lattice3(X1,k5_waybel_0(X0,X2),X3) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l1_orders_2(X1)) )),
% 0.21/0.50    inference(resolution,[],[f73,f71])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X2,k5_waybel_0(X0,X1)) | r1_orders_2(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f51])).
% 0.21/0.50  % (17663)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.50  fof(f508,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r2_lattice3(X0,k5_waybel_0(X0,X1),X2) | ~v12_waybel_0(k5_waybel_0(X0,X1),X0) | ~v1_waybel_0(k5_waybel_0(X0,X1),X0) | v4_waybel_7(X2,X0) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~r2_hidden(X2,k5_waybel_0(X0,X1)) | ~v1_waybel_7(k5_waybel_0(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f507,f68])).
% 0.21/0.50  fof(f507,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_waybel_7(k5_waybel_0(X0,X1),X0) | ~v12_waybel_0(k5_waybel_0(X0,X1),X0) | ~v1_waybel_0(k5_waybel_0(X0,X1),X0) | v4_waybel_7(X2,X0) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~r2_hidden(X2,k5_waybel_0(X0,X1)) | ~r2_lattice3(X0,k5_waybel_0(X0,X1),X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f506,f93])).
% 0.21/0.50  fof(f93,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_xboole_0(k5_waybel_0(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f506,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_waybel_7(k5_waybel_0(X0,X1),X0) | ~v12_waybel_0(k5_waybel_0(X0,X1),X0) | ~v1_waybel_0(k5_waybel_0(X0,X1),X0) | v1_xboole_0(k5_waybel_0(X0,X1)) | v4_waybel_7(X2,X0) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~r2_hidden(X2,k5_waybel_0(X0,X1)) | ~r2_lattice3(X0,k5_waybel_0(X0,X1),X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f503])).
% 0.21/0.50  fof(f503,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_waybel_7(k5_waybel_0(X0,X1),X0) | ~v12_waybel_0(k5_waybel_0(X0,X1),X0) | ~v1_waybel_0(k5_waybel_0(X0,X1),X0) | v1_xboole_0(k5_waybel_0(X0,X1)) | v4_waybel_7(X2,X0) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~r2_hidden(X2,k5_waybel_0(X0,X1)) | ~r2_lattice3(X0,k5_waybel_0(X0,X1),X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(resolution,[],[f299,f95])).
% 0.21/0.50  fof(f299,plain,(
% 0.21/0.50    ( ! [X12,X10,X11] : (~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10))) | ~v1_waybel_7(X11,X10) | ~v12_waybel_0(X11,X10) | ~v1_waybel_0(X11,X10) | v1_xboole_0(X11) | v4_waybel_7(X12,X10) | ~l1_orders_2(X10) | ~v2_lattice3(X10) | ~v1_lattice3(X10) | ~v5_orders_2(X10) | ~v4_orders_2(X10) | ~v3_orders_2(X10) | ~r2_hidden(X12,X11) | ~r2_lattice3(X10,X11,X12)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f291,f99])).
% 0.21/0.50  fof(f291,plain,(
% 0.21/0.50    ( ! [X12,X10,X11] : (~m1_subset_1(X12,u1_struct_0(X10)) | ~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10))) | ~v1_waybel_7(X11,X10) | ~v12_waybel_0(X11,X10) | ~v1_waybel_0(X11,X10) | v1_xboole_0(X11) | v4_waybel_7(X12,X10) | ~l1_orders_2(X10) | ~v2_lattice3(X10) | ~v1_lattice3(X10) | ~v5_orders_2(X10) | ~v4_orders_2(X10) | ~v3_orders_2(X10) | ~r2_hidden(X12,X11) | ~r2_lattice3(X10,X11,X12)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f274])).
% 0.21/0.50  fof(f274,plain,(
% 0.21/0.50    ( ! [X12,X10,X11] : (~m1_subset_1(X12,u1_struct_0(X10)) | ~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10))) | ~v1_waybel_7(X11,X10) | ~v12_waybel_0(X11,X10) | ~v1_waybel_0(X11,X10) | v1_xboole_0(X11) | v4_waybel_7(X12,X10) | ~l1_orders_2(X10) | ~v2_lattice3(X10) | ~v1_lattice3(X10) | ~v5_orders_2(X10) | ~v4_orders_2(X10) | ~v3_orders_2(X10) | ~m1_subset_1(X12,u1_struct_0(X10)) | ~l1_orders_2(X10) | ~v5_orders_2(X10) | ~r2_hidden(X12,X11) | ~r2_lattice3(X10,X11,X12)) )),
% 0.21/0.50    inference(superposition,[],[f102,f263])).
% 0.21/0.50  fof(f263,plain,(
% 0.21/0.50    ( ! [X6,X4,X5] : (k1_yellow_0(X4,X5) = X6 | ~m1_subset_1(X6,u1_struct_0(X4)) | ~l1_orders_2(X4) | ~v5_orders_2(X4) | ~r2_hidden(X6,X5) | ~r2_lattice3(X4,X5,X6)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f258])).
% 0.21/0.50  fof(f258,plain,(
% 0.21/0.50    ( ! [X6,X4,X5] : (~r2_lattice3(X4,X5,X6) | ~m1_subset_1(X6,u1_struct_0(X4)) | ~l1_orders_2(X4) | ~v5_orders_2(X4) | ~r2_hidden(X6,X5) | ~m1_subset_1(X6,u1_struct_0(X4)) | k1_yellow_0(X4,X5) = X6 | k1_yellow_0(X4,X5) = X6 | ~r2_lattice3(X4,X5,X6) | ~m1_subset_1(X6,u1_struct_0(X4)) | ~l1_orders_2(X4) | ~v5_orders_2(X4)) )),
% 0.21/0.50    inference(resolution,[],[f140,f79])).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r1_orders_2(X0,X1,sK3(X0,X1,X2)) | k1_yellow_0(X0,X2) = X1 | ~r2_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f53])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | (~r1_orders_2(X0,X1,sK3(X0,X1,X2)) & r2_lattice3(X0,X2,sK3(X0,X1,X2)) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | ~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f52])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X1,sK3(X0,X1,X2)) & r2_lattice3(X0,X2,sK3(X0,X1,X2)) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | ? [X3] : (~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | ~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.21/0.50    inference(flattening,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | (? [X3] : ((~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1))) & ((! [X4] : ((r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | (~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1)) => (r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1)) & ((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) => (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X4) => r1_orders_2(X0,X1,X4))) & r2_lattice3(X0,X2,X1))))))),
% 0.21/0.50    inference(rectify,[],[f7])).
% 0.21/0.51  % (17659)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1)) => (r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1)) & ((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_yellow_0)).
% 0.21/0.51  fof(f140,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X3,sK3(X0,X2,X1)) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | k1_yellow_0(X0,X1) = X2) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f139,f77])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) | k1_yellow_0(X0,X2) = X1 | ~r2_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f53])).
% 0.21/0.51  fof(f139,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (k1_yellow_0(X0,X1) = X2 | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | r1_orders_2(X0,X3,sK3(X0,X2,X1)) | ~m1_subset_1(sK3(X0,X2,X1),u1_struct_0(X0))) )),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f138])).
% 0.21/0.51  fof(f138,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (k1_yellow_0(X0,X1) = X2 | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | r1_orders_2(X0,X3,sK3(X0,X2,X1)) | ~m1_subset_1(sK3(X0,X2,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.51    inference(resolution,[],[f78,f69])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X1] : (~r2_lattice3(X0,X1,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | r1_orders_2(X0,X4,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f50])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r2_lattice3(X0,X2,sK3(X0,X1,X2)) | k1_yellow_0(X0,X2) = X1 | ~r2_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f53])).
% 0.21/0.51  fof(f102,plain,(
% 0.21/0.51    ( ! [X2,X0] : (~m1_subset_1(k1_yellow_0(X0,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_waybel_7(X2,X0) | ~v12_waybel_0(X2,X0) | ~v1_waybel_0(X2,X0) | v1_xboole_0(X2) | v4_waybel_7(k1_yellow_0(X0,X2),X0) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0)) )),
% 0.21/0.51    inference(equality_resolution,[],[f90])).
% 0.21/0.51  fof(f90,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v4_waybel_7(X1,X0) | k1_yellow_0(X0,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_waybel_7(X2,X0) | ~v12_waybel_0(X2,X0) | ~v1_waybel_0(X2,X0) | v1_xboole_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f57])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (((v4_waybel_7(X1,X0) | ! [X2] : (k1_yellow_0(X0,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_waybel_7(X2,X0) | ~v12_waybel_0(X2,X0) | ~v1_waybel_0(X2,X0) | v1_xboole_0(X2))) & ((k1_yellow_0(X0,sK4(X0,X1)) = X1 & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) & v1_waybel_7(sK4(X0,X1),X0) & v12_waybel_0(sK4(X0,X1),X0) & v1_waybel_0(sK4(X0,X1),X0) & ~v1_xboole_0(sK4(X0,X1))) | ~v4_waybel_7(X1,X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f55,f56])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    ! [X1,X0] : (? [X3] : (k1_yellow_0(X0,X3) = X1 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v1_waybel_7(X3,X0) & v12_waybel_0(X3,X0) & v1_waybel_0(X3,X0) & ~v1_xboole_0(X3)) => (k1_yellow_0(X0,sK4(X0,X1)) = X1 & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) & v1_waybel_7(sK4(X0,X1),X0) & v12_waybel_0(sK4(X0,X1),X0) & v1_waybel_0(sK4(X0,X1),X0) & ~v1_xboole_0(sK4(X0,X1))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (((v4_waybel_7(X1,X0) | ! [X2] : (k1_yellow_0(X0,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_waybel_7(X2,X0) | ~v12_waybel_0(X2,X0) | ~v1_waybel_0(X2,X0) | v1_xboole_0(X2))) & (? [X3] : (k1_yellow_0(X0,X3) = X1 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v1_waybel_7(X3,X0) & v12_waybel_0(X3,X0) & v1_waybel_0(X3,X0) & ~v1_xboole_0(X3)) | ~v4_waybel_7(X1,X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0))),
% 0.21/0.51    inference(rectify,[],[f54])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (((v4_waybel_7(X1,X0) | ! [X2] : (k1_yellow_0(X0,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_waybel_7(X2,X0) | ~v12_waybel_0(X2,X0) | ~v1_waybel_0(X2,X0) | v1_xboole_0(X2))) & (? [X2] : (k1_yellow_0(X0,X2) = X1 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v1_waybel_7(X2,X0) & v12_waybel_0(X2,X0) & v1_waybel_0(X2,X0) & ~v1_xboole_0(X2)) | ~v4_waybel_7(X1,X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((v4_waybel_7(X1,X0) <=> ? [X2] : (k1_yellow_0(X0,X2) = X1 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v1_waybel_7(X2,X0) & v12_waybel_0(X2,X0) & v1_waybel_0(X2,X0) & ~v1_xboole_0(X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0))),
% 0.21/0.51    inference(flattening,[],[f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((v4_waybel_7(X1,X0) <=> ? [X2] : (k1_yellow_0(X0,X2) = X1 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v1_waybel_7(X2,X0) & v12_waybel_0(X2,X0) & v1_waybel_0(X2,X0) & ~v1_xboole_0(X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,axiom,(
% 0.21/0.51    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v1_lattice3(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v4_waybel_7(X1,X0) <=> ? [X2] : (k1_yellow_0(X0,X2) = X1 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v1_waybel_7(X2,X0) & v12_waybel_0(X2,X0) & v1_waybel_0(X2,X0) & ~v1_xboole_0(X2)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_waybel_7)).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (17678)------------------------------
% 0.21/0.51  % (17678)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (17678)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (17678)Memory used [KB]: 1918
% 0.21/0.51  % (17678)Time elapsed: 0.085 s
% 0.21/0.51  % (17678)------------------------------
% 0.21/0.51  % (17678)------------------------------
% 0.21/0.51  % (17656)Success in time 0.153 s
%------------------------------------------------------------------------------
