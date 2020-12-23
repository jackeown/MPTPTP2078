%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:46 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 733 expanded)
%              Number of leaves         :   15 ( 250 expanded)
%              Depth                    :   58
%              Number of atoms          :  834 (5374 expanded)
%              Number of equality atoms :   53 ( 111 expanded)
%              Maximal formula depth    :   15 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f181,plain,(
    $false ),
    inference(subsumption_resolution,[],[f180,f45])).

fof(f45,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ~ r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))
    & r3_lattices(sK0,sK1,sK2)
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v17_lattices(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f36,f35,f34])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))
                & r3_lattices(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_lattices(sK0,k7_lattices(sK0,X2),k7_lattices(sK0,X1))
              & r3_lattices(sK0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l3_lattices(sK0)
      & v17_lattices(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r3_lattices(sK0,k7_lattices(sK0,X2),k7_lattices(sK0,X1))
            & r3_lattices(sK0,X1,X2)
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ~ r3_lattices(sK0,k7_lattices(sK0,X2),k7_lattices(sK0,sK1))
          & r3_lattices(sK0,sK1,X2)
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X2] :
        ( ~ r3_lattices(sK0,k7_lattices(sK0,X2),k7_lattices(sK0,sK1))
        & r3_lattices(sK0,sK1,X2)
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ~ r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))
      & r3_lattices(sK0,sK1,sK2)
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

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
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_lattices)).

fof(f180,plain,(
    v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f179,f48])).

fof(f48,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f179,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f178,f49])).

fof(f49,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f37])).

fof(f178,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f177,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_lattices)).

fof(f177,plain,(
    ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f176,f45])).

fof(f176,plain,
    ( ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f175,f48])).

fof(f175,plain,
    ( ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f174,f50])).

fof(f50,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f37])).

fof(f174,plain,
    ( ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f172,f67])).

fof(f172,plain,
    ( ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f130,f171])).

fof(f171,plain,(
    r1_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f170,f49])).

fof(f170,plain,
    ( r1_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f168,f50])).

fof(f168,plain,
    ( r1_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(superposition,[],[f165,f116])).

fof(f116,plain,(
    sK2 = k1_lattices(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f115,f50])).

fof(f115,plain,
    ( sK2 = k1_lattices(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f112,f49])).

fof(f112,plain,
    ( sK2 = k1_lattices(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(superposition,[],[f75,f111])).

fof(f111,plain,(
    sK1 = k2_lattices(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f110,f49])).

fof(f110,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | sK1 = k2_lattices(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f109,f50])).

fof(f109,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | sK1 = k2_lattices(sK0,sK1,sK2) ),
    inference(resolution,[],[f108,f51])).

fof(f51,plain,(
    r3_lattices(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ r3_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k2_lattices(sK0,X0,X1) = X0 ) ),
    inference(duplicate_literal_removal,[],[f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r3_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k2_lattices(sK0,X0,X1) = X0
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f106,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ r1_lattices(sK0,X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k2_lattices(sK0,X1,X0) = X1
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f93,f45])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k2_lattices(sK0,X1,X0) = X1
      | v2_struct_0(sK0)
      | ~ r1_lattices(sK0,X1,X0) ) ),
    inference(subsumption_resolution,[],[f92,f48])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | k2_lattices(sK0,X1,X0) = X1
      | v2_struct_0(sK0)
      | ~ r1_lattices(sK0,X1,X0) ) ),
    inference(resolution,[],[f91,f46])).

fof(f46,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | k2_lattices(X0,X1,X2) = X1
      | v2_struct_0(X0)
      | ~ r1_lattices(X0,X1,X2) ) ),
    inference(subsumption_resolution,[],[f90,f57])).

fof(f57,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
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
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,plain,(
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

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | k2_lattices(X0,X1,X2) = X1
      | ~ v8_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0) ) ),
    inference(duplicate_literal_removal,[],[f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | k2_lattices(X0,X1,X2) = X1
      | ~ v8_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(resolution,[],[f61,f58])).

fof(f58,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ v9_lattices(X0)
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | k2_lattices(X0,X1,X2) = X1
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_lattices(X0,X1,X2)
                  | k2_lattices(X0,X1,X2) != X1 )
                & ( k2_lattices(X0,X1,X2) = X1
                  | ~ r1_lattices(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k2_lattices(X0,X1,X2) = X1 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k2_lattices(X0,X1,X2) = X1 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_lattices(X0,X1,X2)
              <=> k2_lattices(X0,X1,X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_lattices)).

fof(f106,plain,(
    ! [X0,X1] :
      ( r1_lattices(sK0,X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_lattices(sK0,X1,X0) ) ),
    inference(subsumption_resolution,[],[f105,f45])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r1_lattices(sK0,X1,X0)
      | v2_struct_0(sK0)
      | ~ r3_lattices(sK0,X1,X0) ) ),
    inference(subsumption_resolution,[],[f104,f48])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | r1_lattices(sK0,X1,X0)
      | v2_struct_0(sK0)
      | ~ r3_lattices(sK0,X1,X0) ) ),
    inference(resolution,[],[f103,f46])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,X1,X2)
      | v2_struct_0(X0)
      | ~ r3_lattices(X0,X1,X2) ) ),
    inference(subsumption_resolution,[],[f102,f56])).

fof(f56,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,X1,X2)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0) ) ),
    inference(subsumption_resolution,[],[f101,f57])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,X1,X2)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0) ) ),
    inference(duplicate_literal_removal,[],[f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,X1,X2)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(resolution,[],[f69,f58])).

fof(f69,plain,(
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
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f75,plain,(
    ! [X0,X1] :
      ( k1_lattices(sK0,k2_lattices(sK0,X0,X1),X1) = X1
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f74,f45])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k1_lattices(sK0,k2_lattices(sK0,X0,X1),X1) = X1
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f73,f48])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k1_lattices(sK0,k2_lattices(sK0,X0,X1),X1) = X1
      | ~ l3_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f72,f46])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1) ) ),
    inference(resolution,[],[f63,f57])).

fof(f63,plain,(
    ! [X4,X0,X3] :
      ( ~ v8_lattices(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ( sK4(X0) != k1_lattices(X0,k2_lattices(X0,sK3(X0),sK4(X0)),sK4(X0))
            & m1_subset_1(sK4(X0),u1_struct_0(X0))
            & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f40,f42,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k1_lattices(X0,k2_lattices(X0,sK3(X0),X2),X2) != X2
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k1_lattices(X0,k2_lattices(X0,sK3(X0),X2),X2) != X2
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( sK4(X0) != k1_lattices(X0,k2_lattices(X0,sK3(X0),sK4(X0)),sK4(X0))
        & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

% (5233)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
fof(f26,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v8_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattices)).

fof(f165,plain,(
    ! [X0,X1] :
      ( r1_lattices(sK0,k7_lattices(sK0,k1_lattices(sK0,X1,X0)),k7_lattices(sK0,X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f164,f48])).

fof(f164,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_lattices(sK0,k7_lattices(sK0,k1_lattices(sK0,X1,X0)),k7_lattices(sK0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l3_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f163,f45])).

fof(f163,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_lattices(sK0,k7_lattices(sK0,k1_lattices(sK0,X1,X0)),k7_lattices(sK0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | ~ l3_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f162,f46])).

fof(f162,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_lattices(sK0,k7_lattices(sK0,k1_lattices(sK0,X1,X0)),k7_lattices(sK0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ l3_lattices(sK0) ) ),
    inference(resolution,[],[f161,f55])).

fof(f55,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f161,plain,(
    ! [X0,X1] :
      ( ~ v4_lattices(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r1_lattices(sK0,k7_lattices(sK0,k1_lattices(sK0,X0,X1)),k7_lattices(sK0,X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f160,f48])).

fof(f160,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r1_lattices(sK0,k7_lattices(sK0,k1_lattices(sK0,X0,X1)),k7_lattices(sK0,X0))
      | ~ v4_lattices(sK0)
      | ~ l3_lattices(sK0) ) ),
    inference(resolution,[],[f159,f53])).

fof(f53,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => l2_lattices(X0) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f159,plain,(
    ! [X0,X1] :
      ( ~ l2_lattices(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r1_lattices(sK0,k7_lattices(sK0,k1_lattices(sK0,X0,X1)),k7_lattices(sK0,X0))
      | ~ v4_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f158,f45])).

fof(f158,plain,(
    ! [X0,X1] :
      ( r1_lattices(sK0,k7_lattices(sK0,k1_lattices(sK0,X0,X1)),k7_lattices(sK0,X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l2_lattices(sK0)
      | ~ v4_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f157])).

fof(f157,plain,(
    ! [X0,X1] :
      ( r1_lattices(sK0,k7_lattices(sK0,k1_lattices(sK0,X0,X1)),k7_lattices(sK0,X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l2_lattices(sK0)
      | ~ v4_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f155,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_lattices)).

fof(f155,plain,(
    ! [X0,X1] :
      ( r1_lattices(sK0,k7_lattices(sK0,k3_lattices(sK0,X0,X1)),k7_lattices(sK0,X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f154,f45])).

fof(f154,plain,(
    ! [X0,X1] :
      ( r1_lattices(sK0,k7_lattices(sK0,k3_lattices(sK0,X0,X1)),k7_lattices(sK0,X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f153,f48])).

fof(f153,plain,(
    ! [X0,X1] :
      ( r1_lattices(sK0,k7_lattices(sK0,k3_lattices(sK0,X0,X1)),k7_lattices(sK0,X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f152])).

fof(f152,plain,(
    ! [X0,X1] :
      ( r1_lattices(sK0,k7_lattices(sK0,k3_lattices(sK0,X0,X1)),k7_lattices(sK0,X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f151,f67])).

fof(f151,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
      | r1_lattices(sK0,k7_lattices(sK0,k3_lattices(sK0,X0,X1)),k7_lattices(sK0,X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f150,f45])).

fof(f150,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
      | r1_lattices(sK0,k7_lattices(sK0,k3_lattices(sK0,X0,X1)),k7_lattices(sK0,X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f149,f48])).

fof(f149,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
      | r1_lattices(sK0,k7_lattices(sK0,k3_lattices(sK0,X0,X1)),k7_lattices(sK0,X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f148])).

fof(f148,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
      | r1_lattices(sK0,k7_lattices(sK0,k3_lattices(sK0,X0,X1)),k7_lattices(sK0,X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f147,f67])).

fof(f147,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
      | ~ m1_subset_1(k7_lattices(sK0,X1),u1_struct_0(sK0))
      | r1_lattices(sK0,k7_lattices(sK0,k3_lattices(sK0,X1,X0)),k7_lattices(sK0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f146,f48])).

fof(f146,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
      | ~ m1_subset_1(k7_lattices(sK0,X1),u1_struct_0(sK0))
      | r1_lattices(sK0,k7_lattices(sK0,k3_lattices(sK0,X1,X0)),k7_lattices(sK0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l3_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f145,f45])).

fof(f145,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
      | ~ m1_subset_1(k7_lattices(sK0,X1),u1_struct_0(sK0))
      | r1_lattices(sK0,k7_lattices(sK0,k3_lattices(sK0,X1,X0)),k7_lattices(sK0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | ~ l3_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f144,f46])).

fof(f144,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
      | ~ m1_subset_1(k7_lattices(sK0,X1),u1_struct_0(sK0))
      | r1_lattices(sK0,k7_lattices(sK0,k3_lattices(sK0,X1,X0)),k7_lattices(sK0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ l3_lattices(sK0) ) ),
    inference(resolution,[],[f143,f56])).

fof(f143,plain,(
    ! [X2,X3] :
      ( ~ v6_lattices(sK0)
      | ~ m1_subset_1(k7_lattices(sK0,X3),u1_struct_0(sK0))
      | ~ m1_subset_1(k7_lattices(sK0,X2),u1_struct_0(sK0))
      | r1_lattices(sK0,k7_lattices(sK0,k3_lattices(sK0,X2,X3)),k7_lattices(sK0,X2))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f142,f45])).

fof(f142,plain,(
    ! [X2,X3] :
      ( r1_lattices(sK0,k7_lattices(sK0,k3_lattices(sK0,X2,X3)),k7_lattices(sK0,X2))
      | ~ m1_subset_1(k7_lattices(sK0,X3),u1_struct_0(sK0))
      | ~ m1_subset_1(k7_lattices(sK0,X2),u1_struct_0(sK0))
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f141,f87])).

fof(f87,plain,(
    v8_lattices(sK0) ),
    inference(subsumption_resolution,[],[f86,f45])).

fof(f86,plain,
    ( v8_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f85,f48])).

fof(f85,plain,
    ( v8_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f84])).

fof(f84,plain,
    ( v8_lattices(sK0)
    | v8_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f83,f64])).

fof(f64,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0),u1_struct_0(X0))
      | v8_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f83,plain,
    ( ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | v8_lattices(sK0) ),
    inference(subsumption_resolution,[],[f82,f45])).

fof(f82,plain,
    ( ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | v8_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f81,f48])).

fof(f81,plain,
    ( ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | v8_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f80])).

fof(f80,plain,
    ( ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | v8_lattices(sK0)
    | v8_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f79,f65])).

fof(f65,plain,(
    ! [X0] :
      ( m1_subset_1(sK4(X0),u1_struct_0(X0))
      | v8_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f79,plain,
    ( ~ m1_subset_1(sK4(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | v8_lattices(sK0) ),
    inference(subsumption_resolution,[],[f78,f45])).

fof(f78,plain,
    ( v8_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK0),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f77,f48])).

fof(f77,plain,
    ( v8_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK0),u1_struct_0(sK0)) ),
    inference(trivial_inequality_removal,[],[f76])).

fof(f76,plain,
    ( sK4(sK0) != sK4(sK0)
    | v8_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK0),u1_struct_0(sK0)) ),
    inference(superposition,[],[f66,f75])).

fof(f66,plain,(
    ! [X0] :
      ( sK4(X0) != k1_lattices(X0,k2_lattices(X0,sK3(X0),sK4(X0)),sK4(X0))
      | v8_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f141,plain,(
    ! [X2,X3] :
      ( r1_lattices(sK0,k7_lattices(sK0,k3_lattices(sK0,X2,X3)),k7_lattices(sK0,X2))
      | ~ m1_subset_1(k7_lattices(sK0,X3),u1_struct_0(sK0))
      | ~ m1_subset_1(k7_lattices(sK0,X2),u1_struct_0(sK0))
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f140,f48])).

fof(f140,plain,(
    ! [X2,X3] :
      ( r1_lattices(sK0,k7_lattices(sK0,k3_lattices(sK0,X2,X3)),k7_lattices(sK0,X2))
      | ~ m1_subset_1(k7_lattices(sK0,X3),u1_struct_0(sK0))
      | ~ m1_subset_1(k7_lattices(sK0,X2),u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    inference(superposition,[],[f60,f138])).

fof(f138,plain,(
    ! [X0,X1] :
      ( k7_lattices(sK0,k3_lattices(sK0,X1,X0)) = k4_lattices(sK0,k7_lattices(sK0,X1),k7_lattices(sK0,X0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f137,f45])).

fof(f137,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k7_lattices(sK0,k3_lattices(sK0,X1,X0)) = k4_lattices(sK0,k7_lattices(sK0,X1),k7_lattices(sK0,X0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f136,f46])).

fof(f136,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k7_lattices(sK0,k3_lattices(sK0,X1,X0)) = k4_lattices(sK0,k7_lattices(sK0,X1),k7_lattices(sK0,X0))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f135,f48])).

fof(f135,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | k7_lattices(sK0,k3_lattices(sK0,X1,X0)) = k4_lattices(sK0,k7_lattices(sK0,X1),k7_lattices(sK0,X0))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f59,f47])).

fof(f47,plain,(
    v17_lattices(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ v17_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2))
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_lattices)).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => r1_lattices(X0,k4_lattices(X0,X1,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_lattices)).

fof(f130,plain,
    ( ~ r1_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))
    | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) ),
    inference(resolution,[],[f129,f52])).

fof(f52,plain,(
    ~ r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) ),
    inference(cnf_transformation,[],[f37])).

fof(f129,plain,(
    ! [X0,X1] :
      ( r3_lattices(sK0,X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_lattices(sK0,X1,X0) ) ),
    inference(subsumption_resolution,[],[f128,f45])).

fof(f128,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r3_lattices(sK0,X1,X0)
      | v2_struct_0(sK0)
      | ~ r1_lattices(sK0,X1,X0) ) ),
    inference(subsumption_resolution,[],[f127,f48])).

fof(f127,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | r3_lattices(sK0,X1,X0)
      | v2_struct_0(sK0)
      | ~ r1_lattices(sK0,X1,X0) ) ),
    inference(resolution,[],[f126,f46])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r3_lattices(X0,X1,X2)
      | v2_struct_0(X0)
      | ~ r1_lattices(X0,X1,X2) ) ),
    inference(subsumption_resolution,[],[f125,f56])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r3_lattices(X0,X1,X2)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0) ) ),
    inference(subsumption_resolution,[],[f124,f57])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r3_lattices(X0,X1,X2)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0) ) ),
    inference(duplicate_literal_removal,[],[f123])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r3_lattices(X0,X1,X2)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(resolution,[],[f70,f58])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ v9_lattices(X0)
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r3_lattices(X0,X1,X2)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:30:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (5237)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.50  % (5231)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.50  % (5247)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.50  % (5244)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.50  % (5236)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (5229)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.51  % (5234)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.51  % (5239)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.51  % (5250)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.51  % (5245)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.52  % (5246)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.52  % (5252)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.52  % (5241)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.52  % (5242)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.52  % (5230)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.53  % (5240)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.53  % (5252)Refutation not found, incomplete strategy% (5252)------------------------------
% 0.21/0.53  % (5252)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (5252)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (5252)Memory used [KB]: 10618
% 0.21/0.53  % (5252)Time elapsed: 0.116 s
% 0.21/0.53  % (5252)------------------------------
% 0.21/0.53  % (5252)------------------------------
% 0.21/0.53  % (5238)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.53  % (5243)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.53  % (5235)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.53  % (5248)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.53  % (5249)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.54  % (5248)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f181,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(subsumption_resolution,[],[f180,f45])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ~v2_struct_0(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ((~r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) & r3_lattices(sK0,sK1,sK2) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l3_lattices(sK0) & v17_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f36,f35,f34])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (? [X2] : (~r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) & r3_lattices(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (~r3_lattices(sK0,k7_lattices(sK0,X2),k7_lattices(sK0,X1)) & r3_lattices(sK0,X1,X2) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) & l3_lattices(sK0) & v17_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ? [X1] : (? [X2] : (~r3_lattices(sK0,k7_lattices(sK0,X2),k7_lattices(sK0,X1)) & r3_lattices(sK0,X1,X2) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (~r3_lattices(sK0,k7_lattices(sK0,X2),k7_lattices(sK0,sK1)) & r3_lattices(sK0,sK1,X2) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ? [X2] : (~r3_lattices(sK0,k7_lattices(sK0,X2),k7_lattices(sK0,sK1)) & r3_lattices(sK0,sK1,X2) & m1_subset_1(X2,u1_struct_0(sK0))) => (~r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) & r3_lattices(sK0,sK1,sK2) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (? [X2] : (~r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) & r3_lattices(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f15])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (? [X2] : ((~r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) & r3_lattices(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,negated_conjecture,(
% 0.21/0.54    ~! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_lattices(X0,X1,X2) => r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))))))),
% 0.21/0.54    inference(negated_conjecture,[],[f10])).
% 0.21/0.54  fof(f10,conjecture,(
% 0.21/0.54    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_lattices(X0,X1,X2) => r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_lattices)).
% 0.21/0.54  fof(f180,plain,(
% 0.21/0.54    v2_struct_0(sK0)),
% 0.21/0.54    inference(subsumption_resolution,[],[f179,f48])).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    l3_lattices(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f179,plain,(
% 0.21/0.54    ~l3_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.54    inference(subsumption_resolution,[],[f178,f49])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f178,plain,(
% 0.21/0.54    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.54    inference(resolution,[],[f177,f67])).
% 0.21/0.54  fof(f67,plain,(
% 0.21/0.54    ( ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_lattices)).
% 0.21/0.54  fof(f177,plain,(
% 0.21/0.54    ~m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))),
% 0.21/0.54    inference(subsumption_resolution,[],[f176,f45])).
% 0.21/0.54  fof(f176,plain,(
% 0.21/0.54    ~m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) | v2_struct_0(sK0)),
% 0.21/0.54    inference(subsumption_resolution,[],[f175,f48])).
% 0.21/0.54  fof(f175,plain,(
% 0.21/0.54    ~m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.54    inference(subsumption_resolution,[],[f174,f50])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f174,plain,(
% 0.21/0.54    ~m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.54    inference(resolution,[],[f172,f67])).
% 0.21/0.54  fof(f172,plain,(
% 0.21/0.54    ~m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) | ~m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))),
% 0.21/0.54    inference(subsumption_resolution,[],[f130,f171])).
% 0.21/0.54  fof(f171,plain,(
% 0.21/0.54    r1_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))),
% 0.21/0.54    inference(subsumption_resolution,[],[f170,f49])).
% 0.21/0.54  fof(f170,plain,(
% 0.21/0.54    r1_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) | ~m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.54    inference(subsumption_resolution,[],[f168,f50])).
% 0.21/0.54  fof(f168,plain,(
% 0.21/0.54    r1_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.54    inference(superposition,[],[f165,f116])).
% 0.21/0.54  fof(f116,plain,(
% 0.21/0.54    sK2 = k1_lattices(sK0,sK1,sK2)),
% 0.21/0.54    inference(subsumption_resolution,[],[f115,f50])).
% 0.21/0.54  fof(f115,plain,(
% 0.21/0.54    sK2 = k1_lattices(sK0,sK1,sK2) | ~m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.21/0.54    inference(subsumption_resolution,[],[f112,f49])).
% 0.21/0.54  fof(f112,plain,(
% 0.21/0.54    sK2 = k1_lattices(sK0,sK1,sK2) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.21/0.54    inference(superposition,[],[f75,f111])).
% 0.21/0.54  fof(f111,plain,(
% 0.21/0.54    sK1 = k2_lattices(sK0,sK1,sK2)),
% 0.21/0.54    inference(subsumption_resolution,[],[f110,f49])).
% 0.21/0.54  fof(f110,plain,(
% 0.21/0.54    ~m1_subset_1(sK1,u1_struct_0(sK0)) | sK1 = k2_lattices(sK0,sK1,sK2)),
% 0.21/0.54    inference(subsumption_resolution,[],[f109,f50])).
% 0.21/0.54  fof(f109,plain,(
% 0.21/0.54    ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | sK1 = k2_lattices(sK0,sK1,sK2)),
% 0.21/0.54    inference(resolution,[],[f108,f51])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    r3_lattices(sK0,sK1,sK2)),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f108,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r3_lattices(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,X1) = X0) )),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f107])).
% 0.21/0.54  fof(f107,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_lattices(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,X1) = X0 | ~m1_subset_1(X1,u1_struct_0(sK0))) )),
% 0.21/0.54    inference(resolution,[],[f106,f94])).
% 0.21/0.54  fof(f94,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_lattices(sK0,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k2_lattices(sK0,X1,X0) = X1 | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f93,f45])).
% 0.21/0.54  fof(f93,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k2_lattices(sK0,X1,X0) = X1 | v2_struct_0(sK0) | ~r1_lattices(sK0,X1,X0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f92,f48])).
% 0.21/0.54  fof(f92,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | k2_lattices(sK0,X1,X0) = X1 | v2_struct_0(sK0) | ~r1_lattices(sK0,X1,X0)) )),
% 0.21/0.54    inference(resolution,[],[f91,f46])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    v10_lattices(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f91,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~v10_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | k2_lattices(X0,X1,X2) = X1 | v2_struct_0(X0) | ~r1_lattices(X0,X1,X2)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f90,f57])).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 0.21/0.54    inference(flattening,[],[f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.54    inference(pure_predicate_removal,[],[f13])).
% 0.21/0.54  fof(f13,plain,(
% 0.21/0.54    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.54    inference(pure_predicate_removal,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).
% 0.21/0.54  fof(f90,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | k2_lattices(X0,X1,X2) = X1 | ~v8_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0)) )),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f89])).
% 0.21/0.54  fof(f89,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | k2_lattices(X0,X1,X2) = X1 | ~v8_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.21/0.54    inference(resolution,[],[f61,f58])).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  fof(f61,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~v9_lattices(X0) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | k2_lattices(X0,X1,X2) = X1 | ~v8_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f38])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) != X1) & (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(nnf_transformation,[],[f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_lattices)).
% 0.21/0.54  fof(f106,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_lattices(sK0,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_lattices(sK0,X1,X0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f105,f45])).
% 0.21/0.54  fof(f105,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_lattices(sK0,X1,X0) | v2_struct_0(sK0) | ~r3_lattices(sK0,X1,X0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f104,f48])).
% 0.21/0.54  fof(f104,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | r1_lattices(sK0,X1,X0) | v2_struct_0(sK0) | ~r3_lattices(sK0,X1,X0)) )),
% 0.21/0.54    inference(resolution,[],[f103,f46])).
% 0.21/0.54  fof(f103,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~v10_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r1_lattices(X0,X1,X2) | v2_struct_0(X0) | ~r3_lattices(X0,X1,X2)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f102,f56])).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  fof(f102,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r1_lattices(X0,X1,X2) | ~v6_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f101,f57])).
% 0.21/0.54  fof(f101,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r1_lattices(X0,X1,X2) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0)) )),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f100])).
% 0.21/0.54  fof(f100,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r1_lattices(X0,X1,X2) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.21/0.54    inference(resolution,[],[f69,f58])).
% 0.21/0.54  fof(f69,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~v9_lattices(X0) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r1_lattices(X0,X1,X2) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f44])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(nnf_transformation,[],[f33])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_lattices)).
% 0.21/0.54  fof(f75,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_lattices(sK0,k2_lattices(sK0,X0,X1),X1) = X1 | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f74,f45])).
% 0.21/0.54  fof(f74,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k1_lattices(sK0,k2_lattices(sK0,X0,X1),X1) = X1 | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0))) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f73,f48])).
% 0.21/0.54  fof(f73,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k1_lattices(sK0,k2_lattices(sK0,X0,X1),X1) = X1 | ~l3_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0))) )),
% 0.21/0.54    inference(resolution,[],[f72,f46])).
% 0.21/0.54  fof(f72,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~v10_lattices(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0 | ~l3_lattices(X1) | v2_struct_0(X1) | ~m1_subset_1(X0,u1_struct_0(X1))) )),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f71])).
% 0.21/0.54  fof(f71,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0 | ~l3_lattices(X1) | v2_struct_0(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X1)) )),
% 0.21/0.54    inference(resolution,[],[f63,f57])).
% 0.21/0.54  fof(f63,plain,(
% 0.21/0.54    ( ! [X4,X0,X3] : (~v8_lattices(X0) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f43])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    ! [X0] : (((v8_lattices(X0) | ((sK4(X0) != k1_lattices(X0,k2_lattices(X0,sK3(X0),sK4(X0)),sK4(X0)) & m1_subset_1(sK4(X0),u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f40,f42,f41])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    ! [X0] : (? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k1_lattices(X0,k2_lattices(X0,sK3(X0),X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    ! [X0] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,sK3(X0),X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) => (sK4(X0) != k1_lattices(X0,k2_lattices(X0,sK3(X0),sK4(X0)),sK4(X0)) & m1_subset_1(sK4(X0),u1_struct_0(X0))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ! [X0] : (((v8_lattices(X0) | ? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(rectify,[],[f39])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ! [X0] : (((v8_lattices(X0) | ? [X1] : (? [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v8_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(nnf_transformation,[],[f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f26])).
% 0.21/0.54  % (5233)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v8_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattices)).
% 0.21/0.54  fof(f165,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_lattices(sK0,k7_lattices(sK0,k1_lattices(sK0,X1,X0)),k7_lattices(sK0,X1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f164,f48])).
% 0.21/0.54  fof(f164,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,k7_lattices(sK0,k1_lattices(sK0,X1,X0)),k7_lattices(sK0,X1)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l3_lattices(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f163,f45])).
% 0.21/0.54  fof(f163,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,k7_lattices(sK0,k1_lattices(sK0,X1,X0)),k7_lattices(sK0,X1)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~l3_lattices(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f162,f46])).
% 0.21/0.54  fof(f162,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,k7_lattices(sK0,k1_lattices(sK0,X1,X0)),k7_lattices(sK0,X1)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v10_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0)) )),
% 0.21/0.54    inference(resolution,[],[f161,f55])).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    ( ! [X0] : (v4_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  fof(f161,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v4_lattices(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_lattices(sK0,k7_lattices(sK0,k1_lattices(sK0,X0,X1)),k7_lattices(sK0,X0)) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f160,f48])).
% 0.21/0.54  fof(f160,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_lattices(sK0,k7_lattices(sK0,k1_lattices(sK0,X0,X1)),k7_lattices(sK0,X0)) | ~v4_lattices(sK0) | ~l3_lattices(sK0)) )),
% 0.21/0.54    inference(resolution,[],[f159,f53])).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,plain,(
% 0.21/0.54    ! [X0] : (l3_lattices(X0) => l2_lattices(X0))),
% 0.21/0.54    inference(pure_predicate_removal,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).
% 0.21/0.54  fof(f159,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~l2_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_lattices(sK0,k7_lattices(sK0,k1_lattices(sK0,X0,X1)),k7_lattices(sK0,X0)) | ~v4_lattices(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f158,f45])).
% 0.21/0.54  fof(f158,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_lattices(sK0,k7_lattices(sK0,k1_lattices(sK0,X0,X1)),k7_lattices(sK0,X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l2_lattices(sK0) | ~v4_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f157])).
% 0.21/0.54  fof(f157,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_lattices(sK0,k7_lattices(sK0,k1_lattices(sK0,X0,X1)),k7_lattices(sK0,X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l2_lattices(sK0) | ~v4_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(superposition,[],[f155,f68])).
% 0.21/0.54  fof(f68,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f30])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_lattices)).
% 0.21/0.54  fof(f155,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_lattices(sK0,k7_lattices(sK0,k3_lattices(sK0,X0,X1)),k7_lattices(sK0,X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f154,f45])).
% 0.21/0.54  fof(f154,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_lattices(sK0,k7_lattices(sK0,k3_lattices(sK0,X0,X1)),k7_lattices(sK0,X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f153,f48])).
% 0.21/0.54  fof(f153,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_lattices(sK0,k7_lattices(sK0,k3_lattices(sK0,X0,X1)),k7_lattices(sK0,X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f152])).
% 0.21/0.54  fof(f152,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_lattices(sK0,k7_lattices(sK0,k3_lattices(sK0,X0,X1)),k7_lattices(sK0,X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(resolution,[],[f151,f67])).
% 0.21/0.54  fof(f151,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0)) | r1_lattices(sK0,k7_lattices(sK0,k3_lattices(sK0,X0,X1)),k7_lattices(sK0,X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f150,f45])).
% 0.21/0.54  fof(f150,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0)) | r1_lattices(sK0,k7_lattices(sK0,k3_lattices(sK0,X0,X1)),k7_lattices(sK0,X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f149,f48])).
% 0.21/0.54  fof(f149,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0)) | r1_lattices(sK0,k7_lattices(sK0,k3_lattices(sK0,X0,X1)),k7_lattices(sK0,X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f148])).
% 0.21/0.54  fof(f148,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0)) | r1_lattices(sK0,k7_lattices(sK0,k3_lattices(sK0,X0,X1)),k7_lattices(sK0,X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(resolution,[],[f147,f67])).
% 0.21/0.54  fof(f147,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0)) | ~m1_subset_1(k7_lattices(sK0,X1),u1_struct_0(sK0)) | r1_lattices(sK0,k7_lattices(sK0,k3_lattices(sK0,X1,X0)),k7_lattices(sK0,X1)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f146,f48])).
% 0.21/0.54  fof(f146,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0)) | ~m1_subset_1(k7_lattices(sK0,X1),u1_struct_0(sK0)) | r1_lattices(sK0,k7_lattices(sK0,k3_lattices(sK0,X1,X0)),k7_lattices(sK0,X1)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l3_lattices(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f145,f45])).
% 0.21/0.54  fof(f145,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0)) | ~m1_subset_1(k7_lattices(sK0,X1),u1_struct_0(sK0)) | r1_lattices(sK0,k7_lattices(sK0,k3_lattices(sK0,X1,X0)),k7_lattices(sK0,X1)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~l3_lattices(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f144,f46])).
% 0.21/0.54  fof(f144,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0)) | ~m1_subset_1(k7_lattices(sK0,X1),u1_struct_0(sK0)) | r1_lattices(sK0,k7_lattices(sK0,k3_lattices(sK0,X1,X0)),k7_lattices(sK0,X1)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v10_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0)) )),
% 0.21/0.54    inference(resolution,[],[f143,f56])).
% 0.21/0.54  fof(f143,plain,(
% 0.21/0.54    ( ! [X2,X3] : (~v6_lattices(sK0) | ~m1_subset_1(k7_lattices(sK0,X3),u1_struct_0(sK0)) | ~m1_subset_1(k7_lattices(sK0,X2),u1_struct_0(sK0)) | r1_lattices(sK0,k7_lattices(sK0,k3_lattices(sK0,X2,X3)),k7_lattices(sK0,X2)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0))) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f142,f45])).
% 0.21/0.54  fof(f142,plain,(
% 0.21/0.54    ( ! [X2,X3] : (r1_lattices(sK0,k7_lattices(sK0,k3_lattices(sK0,X2,X3)),k7_lattices(sK0,X2)) | ~m1_subset_1(k7_lattices(sK0,X3),u1_struct_0(sK0)) | ~m1_subset_1(k7_lattices(sK0,X2),u1_struct_0(sK0)) | ~v6_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0))) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f141,f87])).
% 0.21/0.54  fof(f87,plain,(
% 0.21/0.54    v8_lattices(sK0)),
% 0.21/0.54    inference(subsumption_resolution,[],[f86,f45])).
% 0.21/0.54  fof(f86,plain,(
% 0.21/0.54    v8_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.54    inference(subsumption_resolution,[],[f85,f48])).
% 0.21/0.54  fof(f85,plain,(
% 0.21/0.54    v8_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f84])).
% 0.21/0.54  fof(f84,plain,(
% 0.21/0.54    v8_lattices(sK0) | v8_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.54    inference(resolution,[],[f83,f64])).
% 0.21/0.54  fof(f64,plain,(
% 0.21/0.54    ( ! [X0] : (m1_subset_1(sK3(X0),u1_struct_0(X0)) | v8_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f43])).
% 0.21/0.54  fof(f83,plain,(
% 0.21/0.54    ~m1_subset_1(sK3(sK0),u1_struct_0(sK0)) | v8_lattices(sK0)),
% 0.21/0.54    inference(subsumption_resolution,[],[f82,f45])).
% 0.21/0.54  fof(f82,plain,(
% 0.21/0.54    ~m1_subset_1(sK3(sK0),u1_struct_0(sK0)) | v8_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.54    inference(subsumption_resolution,[],[f81,f48])).
% 0.21/0.54  fof(f81,plain,(
% 0.21/0.54    ~m1_subset_1(sK3(sK0),u1_struct_0(sK0)) | v8_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f80])).
% 0.21/0.54  fof(f80,plain,(
% 0.21/0.54    ~m1_subset_1(sK3(sK0),u1_struct_0(sK0)) | v8_lattices(sK0) | v8_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.54    inference(resolution,[],[f79,f65])).
% 0.21/0.54  fof(f65,plain,(
% 0.21/0.54    ( ! [X0] : (m1_subset_1(sK4(X0),u1_struct_0(X0)) | v8_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f43])).
% 0.21/0.54  fof(f79,plain,(
% 0.21/0.54    ~m1_subset_1(sK4(sK0),u1_struct_0(sK0)) | ~m1_subset_1(sK3(sK0),u1_struct_0(sK0)) | v8_lattices(sK0)),
% 0.21/0.54    inference(subsumption_resolution,[],[f78,f45])).
% 0.21/0.54  fof(f78,plain,(
% 0.21/0.54    v8_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(sK3(sK0),u1_struct_0(sK0)) | ~m1_subset_1(sK4(sK0),u1_struct_0(sK0))),
% 0.21/0.54    inference(subsumption_resolution,[],[f77,f48])).
% 0.21/0.54  fof(f77,plain,(
% 0.21/0.54    v8_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(sK3(sK0),u1_struct_0(sK0)) | ~m1_subset_1(sK4(sK0),u1_struct_0(sK0))),
% 0.21/0.54    inference(trivial_inequality_removal,[],[f76])).
% 0.21/0.54  fof(f76,plain,(
% 0.21/0.54    sK4(sK0) != sK4(sK0) | v8_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(sK3(sK0),u1_struct_0(sK0)) | ~m1_subset_1(sK4(sK0),u1_struct_0(sK0))),
% 0.21/0.54    inference(superposition,[],[f66,f75])).
% 0.21/0.54  fof(f66,plain,(
% 0.21/0.54    ( ! [X0] : (sK4(X0) != k1_lattices(X0,k2_lattices(X0,sK3(X0),sK4(X0)),sK4(X0)) | v8_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f43])).
% 0.21/0.54  fof(f141,plain,(
% 0.21/0.54    ( ! [X2,X3] : (r1_lattices(sK0,k7_lattices(sK0,k3_lattices(sK0,X2,X3)),k7_lattices(sK0,X2)) | ~m1_subset_1(k7_lattices(sK0,X3),u1_struct_0(sK0)) | ~m1_subset_1(k7_lattices(sK0,X2),u1_struct_0(sK0)) | ~v8_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0))) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f140,f48])).
% 0.21/0.54  fof(f140,plain,(
% 0.21/0.54    ( ! [X2,X3] : (r1_lattices(sK0,k7_lattices(sK0,k3_lattices(sK0,X2,X3)),k7_lattices(sK0,X2)) | ~m1_subset_1(k7_lattices(sK0,X3),u1_struct_0(sK0)) | ~m1_subset_1(k7_lattices(sK0,X2),u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v8_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0))) )),
% 0.21/0.54    inference(superposition,[],[f60,f138])).
% 0.21/0.54  fof(f138,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k7_lattices(sK0,k3_lattices(sK0,X1,X0)) = k4_lattices(sK0,k7_lattices(sK0,X1),k7_lattices(sK0,X0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f137,f45])).
% 0.21/0.54  fof(f137,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k7_lattices(sK0,k3_lattices(sK0,X1,X0)) = k4_lattices(sK0,k7_lattices(sK0,X1),k7_lattices(sK0,X0)) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f136,f46])).
% 0.21/0.54  fof(f136,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k7_lattices(sK0,k3_lattices(sK0,X1,X0)) = k4_lattices(sK0,k7_lattices(sK0,X1),k7_lattices(sK0,X0)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f135,f48])).
% 0.21/0.54  fof(f135,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | k7_lattices(sK0,k3_lattices(sK0,X1,X0)) = k4_lattices(sK0,k7_lattices(sK0,X1),k7_lattices(sK0,X0)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.54    inference(resolution,[],[f59,f47])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    v17_lattices(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~v17_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_lattices)).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r1_lattices(X0,k4_lattices(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (r1_lattices(X0,k4_lattices(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (r1_lattices(X0,k4_lattices(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0] : ((l3_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => r1_lattices(X0,k4_lattices(X0,X1,X2),X1))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_lattices)).
% 0.21/0.54  fof(f130,plain,(
% 0.21/0.54    ~r1_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) | ~m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) | ~m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))),
% 0.21/0.54    inference(resolution,[],[f129,f52])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    ~r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f129,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r3_lattices(sK0,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_lattices(sK0,X1,X0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f128,f45])).
% 0.21/0.54  fof(f128,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r3_lattices(sK0,X1,X0) | v2_struct_0(sK0) | ~r1_lattices(sK0,X1,X0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f127,f48])).
% 0.21/0.54  fof(f127,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | r3_lattices(sK0,X1,X0) | v2_struct_0(sK0) | ~r1_lattices(sK0,X1,X0)) )),
% 0.21/0.54    inference(resolution,[],[f126,f46])).
% 0.21/0.54  fof(f126,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~v10_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r3_lattices(X0,X1,X2) | v2_struct_0(X0) | ~r1_lattices(X0,X1,X2)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f125,f56])).
% 0.21/0.54  fof(f125,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r3_lattices(X0,X1,X2) | ~v6_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f124,f57])).
% 0.21/0.54  fof(f124,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r3_lattices(X0,X1,X2) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0)) )),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f123])).
% 0.21/0.54  fof(f123,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r3_lattices(X0,X1,X2) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.21/0.54    inference(resolution,[],[f70,f58])).
% 0.21/0.54  fof(f70,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~v9_lattices(X0) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r3_lattices(X0,X1,X2) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f44])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (5248)------------------------------
% 0.21/0.54  % (5248)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (5248)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (5248)Memory used [KB]: 6268
% 0.21/0.54  % (5248)Time elapsed: 0.125 s
% 0.21/0.54  % (5248)------------------------------
% 0.21/0.54  % (5248)------------------------------
% 0.21/0.54  % (5232)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.54  % (5251)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.54  % (5232)Refutation not found, incomplete strategy% (5232)------------------------------
% 0.21/0.54  % (5232)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (5232)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (5232)Memory used [KB]: 10618
% 0.21/0.54  % (5232)Time elapsed: 0.114 s
% 0.21/0.54  % (5232)------------------------------
% 0.21/0.54  % (5232)------------------------------
% 0.21/0.54  % (5227)Success in time 0.176 s
%------------------------------------------------------------------------------
