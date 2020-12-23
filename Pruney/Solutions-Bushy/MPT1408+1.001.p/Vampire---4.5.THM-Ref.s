%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1408+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:53 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 845 expanded)
%              Number of leaves         :   12 ( 305 expanded)
%              Depth                    :   20
%              Number of atoms          :  548 (5723 expanded)
%              Number of equality atoms :   35 (1400 expanded)
%              Maximal formula depth    :   15 (   7 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f125,plain,(
    $false ),
    inference(global_subsumption,[],[f37,f98,f121])).

fof(f121,plain,
    ( ~ r3_lattices(sK1,sK2,sK3)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(resolution,[],[f116,f120])).

fof(f120,plain,(
    ~ r1_lattices(sK1,sK2,sK3) ),
    inference(global_subsumption,[],[f40,f38,f37,f87,f118])).

fof(f118,plain,
    ( ~ r3_lattices(sK1,sK3,sK2)
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | sK2 = sK3
    | ~ r1_lattices(sK1,sK2,sK3)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(resolution,[],[f115,f104])).

fof(f104,plain,(
    ! [X1] :
      ( ~ r1_lattices(sK1,sK3,X1)
      | sK3 = X1
      | ~ r1_lattices(sK1,X1,sK3)
      | ~ m1_subset_1(X1,u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f102,f38])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | X0 = X1
      | ~ r1_lattices(sK1,X0,X1)
      | ~ r1_lattices(sK1,X1,X0) ) ),
    inference(global_subsumption,[],[f36,f34,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | X0 = X1
      | ~ r1_lattices(sK1,X0,X1)
      | v2_struct_0(sK1)
      | ~ l3_lattices(sK1)
      | ~ r1_lattices(sK1,X1,X0) ) ),
    inference(resolution,[],[f100,f35])).

fof(f35,plain,(
    v10_lattices(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( sK2 != sK3
    & k2_filter_0(sK1,sK2) = k2_filter_0(sK1,sK3)
    & m1_subset_1(sK3,u1_struct_0(sK1))
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l3_lattices(sK1)
    & v10_lattices(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f13,f29,f28,f27])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( X1 != X2
                & k2_filter_0(X0,X2) = k2_filter_0(X0,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k2_filter_0(sK1,X2) = k2_filter_0(sK1,X1)
              & m1_subset_1(X2,u1_struct_0(sK1)) )
          & m1_subset_1(X1,u1_struct_0(sK1)) )
      & l3_lattices(sK1)
      & v10_lattices(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( X1 != X2
            & k2_filter_0(sK1,X2) = k2_filter_0(sK1,X1)
            & m1_subset_1(X2,u1_struct_0(sK1)) )
        & m1_subset_1(X1,u1_struct_0(sK1)) )
   => ( ? [X2] :
          ( sK2 != X2
          & k2_filter_0(sK1,X2) = k2_filter_0(sK1,sK2)
          & m1_subset_1(X2,u1_struct_0(sK1)) )
      & m1_subset_1(sK2,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X2] :
        ( sK2 != X2
        & k2_filter_0(sK1,X2) = k2_filter_0(sK1,sK2)
        & m1_subset_1(X2,u1_struct_0(sK1)) )
   => ( sK2 != sK3
      & k2_filter_0(sK1,sK2) = k2_filter_0(sK1,sK3)
      & m1_subset_1(sK3,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k2_filter_0(X0,X2) = k2_filter_0(X0,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k2_filter_0(X0,X2) = k2_filter_0(X0,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( k2_filter_0(X0,X2) = k2_filter_0(X0,X1)
                 => X1 = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( k2_filter_0(X0,X2) = k2_filter_0(X0,X1)
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_filter_1)).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | X1 = X2
      | ~ r1_lattices(X0,X2,X1)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ r1_lattices(X0,X1,X2) ) ),
    inference(duplicate_literal_removal,[],[f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | X1 = X2
      | ~ r1_lattices(X0,X2,X1)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0) ) ),
    inference(resolution,[],[f89,f61])).

fof(f61,plain,(
    ! [X3] :
      ( v4_lattices(X3)
      | v2_struct_0(X3)
      | ~ l3_lattices(X3)
      | ~ v10_lattices(X3) ) ),
    inference(resolution,[],[f47,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v4_lattices(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ sP0(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ sP0(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f47,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(definition_folding,[],[f16,f25])).

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
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f11])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_lattices(X0)
      | ~ r1_lattices(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | X1 = X2
      | ~ r1_lattices(X0,X1,X2)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(resolution,[],[f48,f41])).

fof(f41,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
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

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ l2_lattices(X0)
      | ~ r1_lattices(X0,X2,X1)
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | X1 = X2
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f34,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f36,plain,(
    l3_lattices(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f115,plain,(
    ! [X0] :
      ( r1_lattices(sK1,X0,sK2)
      | ~ r3_lattices(sK1,X0,sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f114,f37])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ r3_lattices(sK1,X0,X1)
      | r1_lattices(sK1,X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ) ),
    inference(global_subsumption,[],[f36,f34,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ l3_lattices(sK1)
      | r1_lattices(sK1,X0,X1)
      | ~ r3_lattices(sK1,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | v2_struct_0(sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f112,f35])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | r1_lattices(X1,X0,X2)
      | ~ r3_lattices(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | r1_lattices(X1,X0,X2)
      | ~ r3_lattices(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1) ) ),
    inference(resolution,[],[f110,f60])).

fof(f60,plain,(
    ! [X2] :
      ( v6_lattices(X2)
      | v2_struct_0(X2)
      | ~ l3_lattices(X2)
      | ~ v10_lattices(X2) ) ),
    inference(resolution,[],[f47,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v6_lattices(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ v6_lattices(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | r1_lattices(X1,X2,X0)
      | ~ r3_lattices(X1,X2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ v10_lattices(X1) ) ),
    inference(duplicate_literal_removal,[],[f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | r1_lattices(X1,X2,X0)
      | ~ r3_lattices(X1,X2,X0)
      | ~ v6_lattices(X1)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1) ) ),
    inference(resolution,[],[f106,f59])).

fof(f59,plain,(
    ! [X1] :
      ( v8_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1) ) ),
    inference(resolution,[],[f47,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v8_lattices(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ v8_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,X1,X2)
      | ~ r3_lattices(X0,X1,X2)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0) ) ),
    inference(duplicate_literal_removal,[],[f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,X1,X2)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0) ) ),
    inference(resolution,[],[f52,f58])).

fof(f58,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0) ) ),
    inference(resolution,[],[f47,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v9_lattices(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ v9_lattices(X0)
      | ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,X1,X2)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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

fof(f87,plain,(
    r3_lattices(sK1,sK3,sK2) ),
    inference(global_subsumption,[],[f37,f71,f86])).

fof(f86,plain,
    ( ~ r3_lattices(sK1,sK2,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | r3_lattices(sK1,sK3,sK2) ),
    inference(duplicate_literal_removal,[],[f82])).

fof(f82,plain,
    ( ~ r3_lattices(sK1,sK2,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | r3_lattices(sK1,sK3,sK2) ),
    inference(resolution,[],[f80,f77])).

fof(f77,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_filter_0(sK1,sK2))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | r3_lattices(sK1,sK3,X1) ) ),
    inference(forward_demodulation,[],[f76,f39])).

fof(f39,plain,(
    k2_filter_0(sK1,sK2) = k2_filter_0(sK1,sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f76,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_filter_0(sK1,sK3))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | r3_lattices(sK1,sK3,X1) ) ),
    inference(resolution,[],[f74,f38])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ r2_hidden(X0,k2_filter_0(sK1,X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | r3_lattices(sK1,X1,X0) ) ),
    inference(global_subsumption,[],[f36,f34,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_filter_0(sK1,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ l3_lattices(sK1)
      | r3_lattices(sK1,X1,X0)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f49,f35])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X0)
      | ~ r2_hidden(X1,k2_filter_0(X0,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r3_lattices(X0,X2,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X1,k2_filter_0(X0,X2))
                  | ~ r3_lattices(X0,X2,X1) )
                & ( r3_lattices(X0,X2,X1)
                  | ~ r2_hidden(X1,k2_filter_0(X0,X2)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X1,k2_filter_0(X0,X2))
              <=> r3_lattices(X0,X2,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X1,k2_filter_0(X0,X2))
              <=> r3_lattices(X0,X2,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X1,k2_filter_0(X0,X2))
              <=> r3_lattices(X0,X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_filter_0)).

fof(f80,plain,(
    ! [X0] :
      ( r2_hidden(sK2,k2_filter_0(sK1,X0))
      | ~ r3_lattices(sK1,X0,sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f79,f37])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ r3_lattices(sK1,X0,X1)
      | r2_hidden(X1,k2_filter_0(sK1,X0)) ) ),
    inference(global_subsumption,[],[f36,f34,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r3_lattices(sK1,X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ l3_lattices(sK1)
      | r2_hidden(X1,k2_filter_0(sK1,X0))
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f50,f35])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X0)
      | ~ r3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r2_hidden(X1,k2_filter_0(X0,X2))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f71,plain,(
    r3_lattices(sK1,sK2,sK2) ),
    inference(resolution,[],[f70,f37])).

fof(f70,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | r3_lattices(sK1,X0,X0) ) ),
    inference(global_subsumption,[],[f36,f35,f34,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | r3_lattices(sK1,X0,X0)
      | v2_struct_0(sK1)
      | ~ l3_lattices(sK1)
      | ~ v10_lattices(sK1) ) ),
    inference(resolution,[],[f68,f60])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v6_lattices(sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | r3_lattices(sK1,X0,X0) ) ),
    inference(global_subsumption,[],[f36,f35,f34,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ v6_lattices(sK1)
      | r3_lattices(sK1,X0,X0)
      | v2_struct_0(sK1)
      | ~ l3_lattices(sK1)
      | ~ v10_lattices(sK1) ) ),
    inference(resolution,[],[f66,f59])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v8_lattices(sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ v6_lattices(sK1)
      | r3_lattices(sK1,X0,X0) ) ),
    inference(global_subsumption,[],[f36,f35,f34,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ v8_lattices(sK1)
      | ~ v6_lattices(sK1)
      | r3_lattices(sK1,X0,X0)
      | v2_struct_0(sK1)
      | ~ l3_lattices(sK1)
      | ~ v10_lattices(sK1) ) ),
    inference(resolution,[],[f64,f58])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v9_lattices(sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ v8_lattices(sK1)
      | ~ v6_lattices(sK1)
      | r3_lattices(sK1,X0,X0) ) ),
    inference(global_subsumption,[],[f36,f34,f63])).

fof(f63,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ l3_lattices(sK1)
      | ~ v9_lattices(sK1)
      | ~ v8_lattices(sK1)
      | ~ v6_lattices(sK1)
      | v2_struct_0(sK1)
      | r3_lattices(sK1,X0,X0) ) ),
    inference(resolution,[],[f55,f56])).

fof(f56,plain,(
    sP4(sK1) ),
    inference(resolution,[],[f54,f37])).

fof(f54,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | sP4(X0) ) ),
    inference(cnf_transformation,[],[f54_D])).

fof(f54_D,plain,(
    ! [X0] :
      ( ! [X2] : ~ m1_subset_1(X2,u1_struct_0(X0))
    <=> ~ sP4(X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP4])])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ sP4(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0)
      | r3_lattices(X0,X1,X1) ) ),
    inference(general_splitting,[],[f51,f54_D])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r3_lattices(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r3_lattices(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => r3_lattices(X0,X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r3_lattices)).

fof(f38,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f40,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f30])).

fof(f116,plain,(
    ! [X1] :
      ( r1_lattices(sK1,X1,sK3)
      | ~ r3_lattices(sK1,X1,sK3)
      | ~ m1_subset_1(X1,u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f114,f38])).

fof(f98,plain,(
    r3_lattices(sK1,sK2,sK3) ),
    inference(global_subsumption,[],[f38,f97])).

fof(f97,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | r3_lattices(sK1,sK2,sK3) ),
    inference(resolution,[],[f95,f75])).

fof(f75,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_filter_0(sK1,sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | r3_lattices(sK1,sK2,X0) ) ),
    inference(resolution,[],[f74,f37])).

fof(f95,plain,(
    r2_hidden(sK3,k2_filter_0(sK1,sK2)) ),
    inference(global_subsumption,[],[f38,f72,f94])).

fof(f94,plain,
    ( r2_hidden(sK3,k2_filter_0(sK1,sK2))
    | ~ r3_lattices(sK1,sK3,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(superposition,[],[f81,f39])).

fof(f81,plain,(
    ! [X1] :
      ( r2_hidden(sK3,k2_filter_0(sK1,X1))
      | ~ r3_lattices(sK1,X1,sK3)
      | ~ m1_subset_1(X1,u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f79,f38])).

fof(f72,plain,(
    r3_lattices(sK1,sK3,sK3) ),
    inference(resolution,[],[f70,f38])).

fof(f37,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f30])).

%------------------------------------------------------------------------------
