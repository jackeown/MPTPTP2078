%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 302 expanded)
%              Number of leaves         :   12 ( 101 expanded)
%              Depth                    :   25
%              Number of atoms          :  542 (2186 expanded)
%              Number of equality atoms :   30 ( 239 expanded)
%              Maximal formula depth    :   24 (   8 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f104,plain,(
    $false ),
    inference(subsumption_resolution,[],[f103,f39])).

fof(f39,plain,(
    l3_lattices(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( sK2 != k16_lattice3(sK1,sK3)
    & r3_lattice3(sK1,sK2,sK3)
    & r2_hidden(sK2,sK3)
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l3_lattices(sK1)
    & v4_lattice3(sK1)
    & v10_lattices(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f14,f32,f31,f30])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k16_lattice3(X0,X2) != X1
                & r3_lattice3(X0,X1,X2)
                & r2_hidden(X1,X2) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k16_lattice3(sK1,X2) != X1
              & r3_lattice3(sK1,X1,X2)
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(sK1)) )
      & l3_lattices(sK1)
      & v4_lattice3(sK1)
      & v10_lattices(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k16_lattice3(sK1,X2) != X1
            & r3_lattice3(sK1,X1,X2)
            & r2_hidden(X1,X2) )
        & m1_subset_1(X1,u1_struct_0(sK1)) )
   => ( ? [X2] :
          ( k16_lattice3(sK1,X2) != sK2
          & r3_lattice3(sK1,sK2,X2)
          & r2_hidden(sK2,X2) )
      & m1_subset_1(sK2,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X2] :
        ( k16_lattice3(sK1,X2) != sK2
        & r3_lattice3(sK1,sK2,X2)
        & r2_hidden(sK2,X2) )
   => ( sK2 != k16_lattice3(sK1,sK3)
      & r3_lattice3(sK1,sK2,sK3)
      & r2_hidden(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k16_lattice3(X0,X2) != X1
              & r3_lattice3(X0,X1,X2)
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k16_lattice3(X0,X2) != X1
              & r3_lattice3(X0,X1,X2)
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
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
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( ( r3_lattice3(X0,X1,X2)
                  & r2_hidden(X1,X2) )
               => k16_lattice3(X0,X2) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( r3_lattice3(X0,X1,X2)
                & r2_hidden(X1,X2) )
             => k16_lattice3(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_lattice3)).

fof(f103,plain,(
    ~ l3_lattices(sK1) ),
    inference(subsumption_resolution,[],[f102,f65])).

fof(f65,plain,(
    v4_lattices(sK1) ),
    inference(resolution,[],[f61,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v4_lattices(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ sP0(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ sP0(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f61,plain,(
    sP0(sK1) ),
    inference(subsumption_resolution,[],[f60,f39])).

fof(f60,plain,
    ( sP0(sK1)
    | ~ l3_lattices(sK1) ),
    inference(subsumption_resolution,[],[f59,f36])).

fof(f36,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f59,plain,
    ( sP0(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK1) ),
    inference(resolution,[],[f50,f37])).

fof(f37,plain,(
    v10_lattices(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | sP0(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(definition_folding,[],[f17,f28])).

fof(f17,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
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
          & v4_lattices(X0)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).

fof(f102,plain,
    ( ~ v4_lattices(sK1)
    | ~ l3_lattices(sK1) ),
    inference(subsumption_resolution,[],[f101,f40])).

fof(f40,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f33])).

fof(f101,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ v4_lattices(sK1)
    | ~ l3_lattices(sK1) ),
    inference(subsumption_resolution,[],[f100,f43])).

fof(f43,plain,(
    sK2 != k16_lattice3(sK1,sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f100,plain,
    ( sK2 = k16_lattice3(sK1,sK3)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ v4_lattices(sK1)
    | ~ l3_lattices(sK1) ),
    inference(subsumption_resolution,[],[f99,f37])).

fof(f99,plain,
    ( ~ v10_lattices(sK1)
    | sK2 = k16_lattice3(sK1,sK3)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ v4_lattices(sK1)
    | ~ l3_lattices(sK1) ),
    inference(subsumption_resolution,[],[f98,f38])).

fof(f38,plain,(
    v4_lattice3(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f98,plain,
    ( ~ v4_lattice3(sK1)
    | ~ v10_lattices(sK1)
    | sK2 = k16_lattice3(sK1,sK3)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ v4_lattices(sK1)
    | ~ l3_lattices(sK1) ),
    inference(subsumption_resolution,[],[f97,f41])).

fof(f41,plain,(
    r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f97,plain,
    ( ~ r2_hidden(sK2,sK3)
    | ~ v4_lattice3(sK1)
    | ~ v10_lattices(sK1)
    | sK2 = k16_lattice3(sK1,sK3)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ v4_lattices(sK1)
    | ~ l3_lattices(sK1) ),
    inference(subsumption_resolution,[],[f96,f36])).

fof(f96,plain,
    ( v2_struct_0(sK1)
    | ~ r2_hidden(sK2,sK3)
    | ~ v4_lattice3(sK1)
    | ~ v10_lattices(sK1)
    | sK2 = k16_lattice3(sK1,sK3)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ v4_lattices(sK1)
    | ~ l3_lattices(sK1) ),
    inference(subsumption_resolution,[],[f95,f64])).

fof(f64,plain,(
    v6_lattices(sK1) ),
    inference(resolution,[],[f61,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v6_lattices(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f95,plain,
    ( ~ v6_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ r2_hidden(sK2,sK3)
    | ~ v4_lattice3(sK1)
    | ~ v10_lattices(sK1)
    | sK2 = k16_lattice3(sK1,sK3)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ v4_lattices(sK1)
    | ~ l3_lattices(sK1) ),
    inference(subsumption_resolution,[],[f94,f63])).

fof(f63,plain,(
    v8_lattices(sK1) ),
    inference(resolution,[],[f61,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v8_lattices(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f94,plain,
    ( ~ v8_lattices(sK1)
    | ~ v6_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ r2_hidden(sK2,sK3)
    | ~ v4_lattice3(sK1)
    | ~ v10_lattices(sK1)
    | sK2 = k16_lattice3(sK1,sK3)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ v4_lattices(sK1)
    | ~ l3_lattices(sK1) ),
    inference(subsumption_resolution,[],[f93,f62])).

fof(f62,plain,(
    v9_lattices(sK1) ),
    inference(resolution,[],[f61,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v9_lattices(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f93,plain,
    ( ~ v9_lattices(sK1)
    | ~ v8_lattices(sK1)
    | ~ v6_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ r2_hidden(sK2,sK3)
    | ~ v4_lattice3(sK1)
    | ~ v10_lattices(sK1)
    | sK2 = k16_lattice3(sK1,sK3)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ v4_lattices(sK1)
    | ~ l3_lattices(sK1) ),
    inference(resolution,[],[f89,f42])).

fof(f42,plain,(
    r3_lattice3(sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f89,plain,(
    ! [X4,X5,X3] :
      ( ~ r3_lattice3(X3,X4,X5)
      | ~ v9_lattices(X3)
      | ~ v8_lattices(X3)
      | ~ v6_lattices(X3)
      | v2_struct_0(X3)
      | ~ r2_hidden(X4,X5)
      | ~ v4_lattice3(X3)
      | ~ v10_lattices(X3)
      | k16_lattice3(X3,X5) = X4
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ v4_lattices(X3)
      | ~ l3_lattices(X3) ) ),
    inference(duplicate_literal_removal,[],[f88])).

fof(f88,plain,(
    ! [X4,X5,X3] :
      ( ~ l3_lattices(X3)
      | ~ v9_lattices(X3)
      | ~ v8_lattices(X3)
      | ~ v6_lattices(X3)
      | v2_struct_0(X3)
      | ~ r2_hidden(X4,X5)
      | ~ v4_lattice3(X3)
      | ~ v10_lattices(X3)
      | k16_lattice3(X3,X5) = X4
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ v4_lattices(X3)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ l3_lattices(X3)
      | ~ v9_lattices(X3)
      | ~ v8_lattices(X3)
      | ~ v6_lattices(X3)
      | v2_struct_0(X3)
      | ~ r3_lattice3(X3,X4,X5)
      | ~ v4_lattice3(X3)
      | ~ v10_lattices(X3) ) ),
    inference(resolution,[],[f80,f73])).

fof(f73,plain,(
    ! [X4,X5,X3] :
      ( r1_lattices(X3,X4,k16_lattice3(X3,X5))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ l3_lattices(X3)
      | ~ v9_lattices(X3)
      | ~ v8_lattices(X3)
      | ~ v6_lattices(X3)
      | v2_struct_0(X3)
      | ~ r3_lattice3(X3,X4,X5)
      | ~ v4_lattice3(X3)
      | ~ v10_lattices(X3) ) ),
    inference(subsumption_resolution,[],[f71,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k16_lattice3)).

fof(f71,plain,(
    ! [X4,X5,X3] :
      ( r1_lattices(X3,X4,k16_lattice3(X3,X5))
      | ~ m1_subset_1(k16_lattice3(X3,X5),u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ l3_lattices(X3)
      | ~ v9_lattices(X3)
      | ~ v8_lattices(X3)
      | ~ v6_lattices(X3)
      | v2_struct_0(X3)
      | ~ r3_lattice3(X3,X4,X5)
      | ~ v4_lattice3(X3)
      | ~ v10_lattices(X3) ) ),
    inference(duplicate_literal_removal,[],[f68])).

fof(f68,plain,(
    ! [X4,X5,X3] :
      ( r1_lattices(X3,X4,k16_lattice3(X3,X5))
      | ~ m1_subset_1(k16_lattice3(X3,X5),u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ l3_lattices(X3)
      | ~ v9_lattices(X3)
      | ~ v8_lattices(X3)
      | ~ v6_lattices(X3)
      | v2_struct_0(X3)
      | ~ r3_lattice3(X3,X4,X5)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ l3_lattices(X3)
      | ~ v4_lattice3(X3)
      | ~ v10_lattices(X3)
      | v2_struct_0(X3) ) ),
    inference(resolution,[],[f56,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,X1,k16_lattice3(X0,X2))
      | ~ r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_lattices(X0,X1,k16_lattice3(X0,X2))
              | ~ r3_lattice3(X0,X1,X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_lattices(X0,X1,k16_lattice3(X0,X2))
              | ~ r3_lattice3(X0,X1,X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
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
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r3_lattice3(X0,X1,X2)
             => r3_lattices(X0,X1,k16_lattice3(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_lattice3)).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_lattices(X0,X1,X2)
      | r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_lattices(X0,X1,X2)
          | ~ r1_lattices(X0,X1,X2) )
        & ( r1_lattices(X0,X1,X2)
          | ~ r3_lattices(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_lattices)).

fof(f80,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_lattices(X4,X3,k16_lattice3(X4,X5))
      | ~ l3_lattices(X4)
      | ~ v9_lattices(X4)
      | ~ v8_lattices(X4)
      | ~ v6_lattices(X4)
      | v2_struct_0(X4)
      | ~ r2_hidden(X3,X5)
      | ~ v4_lattice3(X4)
      | ~ v10_lattices(X4)
      | k16_lattice3(X4,X5) = X3
      | ~ m1_subset_1(X3,u1_struct_0(X4))
      | ~ v4_lattices(X4) ) ),
    inference(subsumption_resolution,[],[f79,f55])).

fof(f79,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(X4))
      | ~ l3_lattices(X4)
      | ~ v9_lattices(X4)
      | ~ v8_lattices(X4)
      | ~ v6_lattices(X4)
      | v2_struct_0(X4)
      | ~ r2_hidden(X3,X5)
      | ~ v4_lattice3(X4)
      | ~ v10_lattices(X4)
      | k16_lattice3(X4,X5) = X3
      | ~ r1_lattices(X4,X3,k16_lattice3(X4,X5))
      | ~ m1_subset_1(k16_lattice3(X4,X5),u1_struct_0(X4))
      | ~ v4_lattices(X4) ) ),
    inference(subsumption_resolution,[],[f77,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | l2_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => l2_lattices(X0) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f77,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(X4))
      | ~ l3_lattices(X4)
      | ~ v9_lattices(X4)
      | ~ v8_lattices(X4)
      | ~ v6_lattices(X4)
      | v2_struct_0(X4)
      | ~ r2_hidden(X3,X5)
      | ~ v4_lattice3(X4)
      | ~ v10_lattices(X4)
      | k16_lattice3(X4,X5) = X3
      | ~ r1_lattices(X4,X3,k16_lattice3(X4,X5))
      | ~ m1_subset_1(k16_lattice3(X4,X5),u1_struct_0(X4))
      | ~ l2_lattices(X4)
      | ~ v4_lattices(X4) ) ),
    inference(duplicate_literal_removal,[],[f76])).

fof(f76,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(X4))
      | ~ l3_lattices(X4)
      | ~ v9_lattices(X4)
      | ~ v8_lattices(X4)
      | ~ v6_lattices(X4)
      | v2_struct_0(X4)
      | ~ r2_hidden(X3,X5)
      | ~ v4_lattice3(X4)
      | ~ v10_lattices(X4)
      | k16_lattice3(X4,X5) = X3
      | ~ r1_lattices(X4,X3,k16_lattice3(X4,X5))
      | ~ m1_subset_1(k16_lattice3(X4,X5),u1_struct_0(X4))
      | ~ m1_subset_1(X3,u1_struct_0(X4))
      | ~ l2_lattices(X4)
      | ~ v4_lattices(X4)
      | v2_struct_0(X4) ) ),
    inference(resolution,[],[f74,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X2,X1)
      | X1 = X2
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_lattices(X0,X2,X1)
              | ~ r1_lattices(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_lattices(X0,X2,X1)
              | ~ r1_lattices(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_lattices)).

fof(f74,plain,(
    ! [X6,X8,X7] :
      ( r1_lattices(X6,k16_lattice3(X6,X7),X8)
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ l3_lattices(X6)
      | ~ v9_lattices(X6)
      | ~ v8_lattices(X6)
      | ~ v6_lattices(X6)
      | v2_struct_0(X6)
      | ~ r2_hidden(X8,X7)
      | ~ v4_lattice3(X6)
      | ~ v10_lattices(X6) ) ),
    inference(subsumption_resolution,[],[f70,f55])).

fof(f70,plain,(
    ! [X6,X8,X7] :
      ( r1_lattices(X6,k16_lattice3(X6,X7),X8)
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ m1_subset_1(k16_lattice3(X6,X7),u1_struct_0(X6))
      | ~ l3_lattices(X6)
      | ~ v9_lattices(X6)
      | ~ v8_lattices(X6)
      | ~ v6_lattices(X6)
      | v2_struct_0(X6)
      | ~ r2_hidden(X8,X7)
      | ~ v4_lattice3(X6)
      | ~ v10_lattices(X6) ) ),
    inference(duplicate_literal_removal,[],[f69])).

fof(f69,plain,(
    ! [X6,X8,X7] :
      ( r1_lattices(X6,k16_lattice3(X6,X7),X8)
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ m1_subset_1(k16_lattice3(X6,X7),u1_struct_0(X6))
      | ~ l3_lattices(X6)
      | ~ v9_lattices(X6)
      | ~ v8_lattices(X6)
      | ~ v6_lattices(X6)
      | v2_struct_0(X6)
      | ~ r2_hidden(X8,X7)
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ l3_lattices(X6)
      | ~ v4_lattice3(X6)
      | ~ v10_lattices(X6)
      | v2_struct_0(X6) ) ),
    inference(resolution,[],[f56,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:40:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (29072)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.47  % (29056)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.48  % (29061)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (29053)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.49  % (29053)Refutation not found, incomplete strategy% (29053)------------------------------
% 0.21/0.49  % (29053)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (29053)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (29053)Memory used [KB]: 10490
% 0.21/0.49  % (29053)Time elapsed: 0.003 s
% 0.21/0.49  % (29053)------------------------------
% 0.21/0.49  % (29053)------------------------------
% 0.21/0.49  % (29072)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f104,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(subsumption_resolution,[],[f103,f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    l3_lattices(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ((sK2 != k16_lattice3(sK1,sK3) & r3_lattice3(sK1,sK2,sK3) & r2_hidden(sK2,sK3)) & m1_subset_1(sK2,u1_struct_0(sK1))) & l3_lattices(sK1) & v4_lattice3(sK1) & v10_lattices(sK1) & ~v2_struct_0(sK1)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f14,f32,f31,f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k16_lattice3(sK1,X2) != X1 & r3_lattice3(sK1,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(sK1))) & l3_lattices(sK1) & v4_lattice3(sK1) & v10_lattices(sK1) & ~v2_struct_0(sK1))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ? [X1] : (? [X2] : (k16_lattice3(sK1,X2) != X1 & r3_lattice3(sK1,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(sK1))) => (? [X2] : (k16_lattice3(sK1,X2) != sK2 & r3_lattice3(sK1,sK2,X2) & r2_hidden(sK2,X2)) & m1_subset_1(sK2,u1_struct_0(sK1)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ? [X2] : (k16_lattice3(sK1,X2) != sK2 & r3_lattice3(sK1,sK2,X2) & r2_hidden(sK2,X2)) => (sK2 != k16_lattice3(sK1,sK3) & r3_lattice3(sK1,sK2,sK3) & r2_hidden(sK2,sK3))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & (r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,negated_conjecture,(
% 0.21/0.49    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) => k16_lattice3(X0,X2) = X1)))),
% 0.21/0.49    inference(negated_conjecture,[],[f8])).
% 0.21/0.49  fof(f8,conjecture,(
% 0.21/0.49    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) => k16_lattice3(X0,X2) = X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_lattice3)).
% 0.21/0.49  fof(f103,plain,(
% 0.21/0.49    ~l3_lattices(sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f102,f65])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    v4_lattices(sK1)),
% 0.21/0.49    inference(resolution,[],[f61,f46])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ( ! [X0] : (~sP0(X0) | v4_lattices(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~sP0(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~sP0(X0))),
% 0.21/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    sP0(sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f60,f39])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    sP0(sK1) | ~l3_lattices(sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f59,f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ~v2_struct_0(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f33])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    sP0(sK1) | v2_struct_0(sK1) | ~l3_lattices(sK1)),
% 0.21/0.49    inference(resolution,[],[f50,f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    v10_lattices(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f33])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ( ! [X0] : (~v10_lattices(X0) | sP0(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ! [X0] : (sP0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 0.21/0.49    inference(definition_folding,[],[f17,f28])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 0.21/0.49    inference(flattening,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.49    inference(pure_predicate_removal,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.49    inference(pure_predicate_removal,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).
% 0.21/0.49  fof(f102,plain,(
% 0.21/0.49    ~v4_lattices(sK1) | ~l3_lattices(sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f101,f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    m1_subset_1(sK2,u1_struct_0(sK1))),
% 0.21/0.49    inference(cnf_transformation,[],[f33])).
% 0.21/0.49  fof(f101,plain,(
% 0.21/0.49    ~m1_subset_1(sK2,u1_struct_0(sK1)) | ~v4_lattices(sK1) | ~l3_lattices(sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f100,f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    sK2 != k16_lattice3(sK1,sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f33])).
% 0.21/0.49  fof(f100,plain,(
% 0.21/0.49    sK2 = k16_lattice3(sK1,sK3) | ~m1_subset_1(sK2,u1_struct_0(sK1)) | ~v4_lattices(sK1) | ~l3_lattices(sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f99,f37])).
% 0.21/0.49  fof(f99,plain,(
% 0.21/0.49    ~v10_lattices(sK1) | sK2 = k16_lattice3(sK1,sK3) | ~m1_subset_1(sK2,u1_struct_0(sK1)) | ~v4_lattices(sK1) | ~l3_lattices(sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f98,f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    v4_lattice3(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f33])).
% 0.21/0.49  fof(f98,plain,(
% 0.21/0.49    ~v4_lattice3(sK1) | ~v10_lattices(sK1) | sK2 = k16_lattice3(sK1,sK3) | ~m1_subset_1(sK2,u1_struct_0(sK1)) | ~v4_lattices(sK1) | ~l3_lattices(sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f97,f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    r2_hidden(sK2,sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f33])).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    ~r2_hidden(sK2,sK3) | ~v4_lattice3(sK1) | ~v10_lattices(sK1) | sK2 = k16_lattice3(sK1,sK3) | ~m1_subset_1(sK2,u1_struct_0(sK1)) | ~v4_lattices(sK1) | ~l3_lattices(sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f96,f36])).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    v2_struct_0(sK1) | ~r2_hidden(sK2,sK3) | ~v4_lattice3(sK1) | ~v10_lattices(sK1) | sK2 = k16_lattice3(sK1,sK3) | ~m1_subset_1(sK2,u1_struct_0(sK1)) | ~v4_lattices(sK1) | ~l3_lattices(sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f95,f64])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    v6_lattices(sK1)),
% 0.21/0.49    inference(resolution,[],[f61,f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ( ! [X0] : (~sP0(X0) | v6_lattices(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f34])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    ~v6_lattices(sK1) | v2_struct_0(sK1) | ~r2_hidden(sK2,sK3) | ~v4_lattice3(sK1) | ~v10_lattices(sK1) | sK2 = k16_lattice3(sK1,sK3) | ~m1_subset_1(sK2,u1_struct_0(sK1)) | ~v4_lattices(sK1) | ~l3_lattices(sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f94,f63])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    v8_lattices(sK1)),
% 0.21/0.49    inference(resolution,[],[f61,f48])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ( ! [X0] : (~sP0(X0) | v8_lattices(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f34])).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    ~v8_lattices(sK1) | ~v6_lattices(sK1) | v2_struct_0(sK1) | ~r2_hidden(sK2,sK3) | ~v4_lattice3(sK1) | ~v10_lattices(sK1) | sK2 = k16_lattice3(sK1,sK3) | ~m1_subset_1(sK2,u1_struct_0(sK1)) | ~v4_lattices(sK1) | ~l3_lattices(sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f93,f62])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    v9_lattices(sK1)),
% 0.21/0.49    inference(resolution,[],[f61,f49])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ( ! [X0] : (~sP0(X0) | v9_lattices(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f34])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    ~v9_lattices(sK1) | ~v8_lattices(sK1) | ~v6_lattices(sK1) | v2_struct_0(sK1) | ~r2_hidden(sK2,sK3) | ~v4_lattice3(sK1) | ~v10_lattices(sK1) | sK2 = k16_lattice3(sK1,sK3) | ~m1_subset_1(sK2,u1_struct_0(sK1)) | ~v4_lattices(sK1) | ~l3_lattices(sK1)),
% 0.21/0.49    inference(resolution,[],[f89,f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    r3_lattice3(sK1,sK2,sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f33])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    ( ! [X4,X5,X3] : (~r3_lattice3(X3,X4,X5) | ~v9_lattices(X3) | ~v8_lattices(X3) | ~v6_lattices(X3) | v2_struct_0(X3) | ~r2_hidden(X4,X5) | ~v4_lattice3(X3) | ~v10_lattices(X3) | k16_lattice3(X3,X5) = X4 | ~m1_subset_1(X4,u1_struct_0(X3)) | ~v4_lattices(X3) | ~l3_lattices(X3)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f88])).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    ( ! [X4,X5,X3] : (~l3_lattices(X3) | ~v9_lattices(X3) | ~v8_lattices(X3) | ~v6_lattices(X3) | v2_struct_0(X3) | ~r2_hidden(X4,X5) | ~v4_lattice3(X3) | ~v10_lattices(X3) | k16_lattice3(X3,X5) = X4 | ~m1_subset_1(X4,u1_struct_0(X3)) | ~v4_lattices(X3) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~l3_lattices(X3) | ~v9_lattices(X3) | ~v8_lattices(X3) | ~v6_lattices(X3) | v2_struct_0(X3) | ~r3_lattice3(X3,X4,X5) | ~v4_lattice3(X3) | ~v10_lattices(X3)) )),
% 0.21/0.49    inference(resolution,[],[f80,f73])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    ( ! [X4,X5,X3] : (r1_lattices(X3,X4,k16_lattice3(X3,X5)) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~l3_lattices(X3) | ~v9_lattices(X3) | ~v8_lattices(X3) | ~v6_lattices(X3) | v2_struct_0(X3) | ~r3_lattice3(X3,X4,X5) | ~v4_lattice3(X3) | ~v10_lattices(X3)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f71,f55])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ( ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k16_lattice3)).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    ( ! [X4,X5,X3] : (r1_lattices(X3,X4,k16_lattice3(X3,X5)) | ~m1_subset_1(k16_lattice3(X3,X5),u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~l3_lattices(X3) | ~v9_lattices(X3) | ~v8_lattices(X3) | ~v6_lattices(X3) | v2_struct_0(X3) | ~r3_lattice3(X3,X4,X5) | ~v4_lattice3(X3) | ~v10_lattices(X3)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f68])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    ( ! [X4,X5,X3] : (r1_lattices(X3,X4,k16_lattice3(X3,X5)) | ~m1_subset_1(k16_lattice3(X3,X5),u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~l3_lattices(X3) | ~v9_lattices(X3) | ~v8_lattices(X3) | ~v6_lattices(X3) | v2_struct_0(X3) | ~r3_lattice3(X3,X4,X5) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~l3_lattices(X3) | ~v4_lattice3(X3) | ~v10_lattices(X3) | v2_struct_0(X3)) )),
% 0.21/0.49    inference(resolution,[],[f56,f54])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r3_lattices(X0,X1,k16_lattice3(X0,X2)) | ~r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (r3_lattices(X0,X1,k16_lattice3(X0,X2)) | ~r3_lattice3(X0,X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (r3_lattices(X0,X1,k16_lattice3(X0,X2)) | ~r3_lattice3(X0,X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) => r3_lattices(X0,X1,k16_lattice3(X0,X2)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_lattice3)).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r3_lattices(X0,X1,X2) | r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_lattices)).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    ( ! [X4,X5,X3] : (~r1_lattices(X4,X3,k16_lattice3(X4,X5)) | ~l3_lattices(X4) | ~v9_lattices(X4) | ~v8_lattices(X4) | ~v6_lattices(X4) | v2_struct_0(X4) | ~r2_hidden(X3,X5) | ~v4_lattice3(X4) | ~v10_lattices(X4) | k16_lattice3(X4,X5) = X3 | ~m1_subset_1(X3,u1_struct_0(X4)) | ~v4_lattices(X4)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f79,f55])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    ( ! [X4,X5,X3] : (~m1_subset_1(X3,u1_struct_0(X4)) | ~l3_lattices(X4) | ~v9_lattices(X4) | ~v8_lattices(X4) | ~v6_lattices(X4) | v2_struct_0(X4) | ~r2_hidden(X3,X5) | ~v4_lattice3(X4) | ~v10_lattices(X4) | k16_lattice3(X4,X5) = X3 | ~r1_lattices(X4,X3,k16_lattice3(X4,X5)) | ~m1_subset_1(k16_lattice3(X4,X5),u1_struct_0(X4)) | ~v4_lattices(X4)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f77,f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ( ! [X0] : (~l3_lattices(X0) | l2_lattices(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ! [X0] : (l3_lattices(X0) => l2_lattices(X0))),
% 0.21/0.49    inference(pure_predicate_removal,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    ( ! [X4,X5,X3] : (~m1_subset_1(X3,u1_struct_0(X4)) | ~l3_lattices(X4) | ~v9_lattices(X4) | ~v8_lattices(X4) | ~v6_lattices(X4) | v2_struct_0(X4) | ~r2_hidden(X3,X5) | ~v4_lattice3(X4) | ~v10_lattices(X4) | k16_lattice3(X4,X5) = X3 | ~r1_lattices(X4,X3,k16_lattice3(X4,X5)) | ~m1_subset_1(k16_lattice3(X4,X5),u1_struct_0(X4)) | ~l2_lattices(X4) | ~v4_lattices(X4)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f76])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    ( ! [X4,X5,X3] : (~m1_subset_1(X3,u1_struct_0(X4)) | ~l3_lattices(X4) | ~v9_lattices(X4) | ~v8_lattices(X4) | ~v6_lattices(X4) | v2_struct_0(X4) | ~r2_hidden(X3,X5) | ~v4_lattice3(X4) | ~v10_lattices(X4) | k16_lattice3(X4,X5) = X3 | ~r1_lattices(X4,X3,k16_lattice3(X4,X5)) | ~m1_subset_1(k16_lattice3(X4,X5),u1_struct_0(X4)) | ~m1_subset_1(X3,u1_struct_0(X4)) | ~l2_lattices(X4) | ~v4_lattices(X4) | v2_struct_0(X4)) )),
% 0.21/0.49    inference(resolution,[],[f74,f51])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r1_lattices(X0,X2,X1) | X1 = X2 | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (X1 = X2 | ~r1_lattices(X0,X2,X1) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((X1 = X2 | (~r1_lattices(X0,X2,X1) | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0] : ((l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r1_lattices(X0,X2,X1) & r1_lattices(X0,X1,X2)) => X1 = X2))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_lattices)).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    ( ! [X6,X8,X7] : (r1_lattices(X6,k16_lattice3(X6,X7),X8) | ~m1_subset_1(X8,u1_struct_0(X6)) | ~l3_lattices(X6) | ~v9_lattices(X6) | ~v8_lattices(X6) | ~v6_lattices(X6) | v2_struct_0(X6) | ~r2_hidden(X8,X7) | ~v4_lattice3(X6) | ~v10_lattices(X6)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f70,f55])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    ( ! [X6,X8,X7] : (r1_lattices(X6,k16_lattice3(X6,X7),X8) | ~m1_subset_1(X8,u1_struct_0(X6)) | ~m1_subset_1(k16_lattice3(X6,X7),u1_struct_0(X6)) | ~l3_lattices(X6) | ~v9_lattices(X6) | ~v8_lattices(X6) | ~v6_lattices(X6) | v2_struct_0(X6) | ~r2_hidden(X8,X7) | ~v4_lattice3(X6) | ~v10_lattices(X6)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f69])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    ( ! [X6,X8,X7] : (r1_lattices(X6,k16_lattice3(X6,X7),X8) | ~m1_subset_1(X8,u1_struct_0(X6)) | ~m1_subset_1(k16_lattice3(X6,X7),u1_struct_0(X6)) | ~l3_lattices(X6) | ~v9_lattices(X6) | ~v8_lattices(X6) | ~v6_lattices(X6) | v2_struct_0(X6) | ~r2_hidden(X8,X7) | ~m1_subset_1(X8,u1_struct_0(X6)) | ~l3_lattices(X6) | ~v4_lattice3(X6) | ~v10_lattices(X6) | v2_struct_0(X6)) )),
% 0.21/0.49    inference(resolution,[],[f56,f53])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r3_lattices(X0,k16_lattice3(X0,X2),X1) | ~r2_hidden(X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r2_hidden(X1,X2) => (r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_lattice3)).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (29072)------------------------------
% 0.21/0.49  % (29072)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (29072)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (29072)Memory used [KB]: 10618
% 0.21/0.49  % (29072)Time elapsed: 0.069 s
% 0.21/0.49  % (29072)------------------------------
% 0.21/0.49  % (29072)------------------------------
% 0.21/0.49  % (29046)Success in time 0.123 s
%------------------------------------------------------------------------------
