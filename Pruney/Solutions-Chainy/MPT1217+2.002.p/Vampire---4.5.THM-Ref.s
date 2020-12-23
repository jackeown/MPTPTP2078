%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:45 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 664 expanded)
%              Number of leaves         :   14 ( 227 expanded)
%              Depth                    :   52
%              Number of atoms          :  807 (4845 expanded)
%              Number of equality atoms :   87 (  87 expanded)
%              Maximal formula depth    :   15 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f266,plain,(
    $false ),
    inference(subsumption_resolution,[],[f265,f46])).

fof(f46,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ~ r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))
    & r3_lattices(sK0,sK1,sK2)
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v17_lattices(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f38,f37,f36])).

fof(f36,plain,
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

fof(f37,plain,
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

fof(f38,plain,
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
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
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

fof(f265,plain,(
    ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f264,f43])).

fof(f43,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f264,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f263,f44])).

fof(f44,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f263,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f262,f54])).

fof(f54,plain,(
    ! [X0] :
      ( v4_lattices(X0)
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

fof(f262,plain,(
    ~ v4_lattices(sK0) ),
    inference(subsumption_resolution,[],[f261,f46])).

fof(f261,plain,
    ( ~ v4_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f260,f52])).

fof(f52,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f260,plain,
    ( ~ l2_lattices(sK0)
    | ~ v4_lattices(sK0) ),
    inference(trivial_inequality_removal,[],[f259])).

fof(f259,plain,
    ( k7_lattices(sK0,sK2) != k7_lattices(sK0,sK2)
    | ~ l2_lattices(sK0)
    | ~ v4_lattices(sK0) ),
    inference(forward_demodulation,[],[f258,f163])).

fof(f163,plain,(
    sK2 = k3_lattices(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f162,f47])).

fof(f47,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f39])).

fof(f162,plain,
    ( sK2 = k3_lattices(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f158,f48])).

fof(f48,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f39])).

fof(f158,plain,
    ( sK2 = k3_lattices(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(superposition,[],[f157,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k3_lattices(sK0,X0,X1) = k1_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f73,f46])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k3_lattices(sK0,X0,X1) = k1_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f72,f43])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k3_lattices(sK0,X0,X1) = k1_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f71,f44])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X1)
      | k3_lattices(X1,X0,X2) = k1_lattices(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ l3_lattices(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | k3_lattices(X1,X0,X2) = k1_lattices(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1) ) ),
    inference(resolution,[],[f69,f54])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_lattices(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | k3_lattices(X1,X2,X0) = k1_lattices(X1,X2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ l3_lattices(X1) ) ),
    inference(resolution,[],[f67,f52])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ l2_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_lattices)).

fof(f157,plain,(
    sK2 = k1_lattices(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f156,f46])).

fof(f156,plain,
    ( sK2 = k1_lattices(sK0,sK1,sK2)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f148,f52])).

fof(f148,plain,
    ( ~ l2_lattices(sK0)
    | sK2 = k1_lattices(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f147,f43])).

fof(f147,plain,
    ( sK2 = k1_lattices(sK0,sK1,sK2)
    | ~ l2_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f146,f47])).

fof(f146,plain,
    ( sK2 = k1_lattices(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l2_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f143,f48])).

fof(f143,plain,
    ( sK2 = k1_lattices(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l2_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f141,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X1,X2)
      | k1_lattices(X0,X1,X2) = X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_lattices(X0,X1,X2)
                  | k1_lattices(X0,X1,X2) != X2 )
                & ( k1_lattices(X0,X1,X2) = X2
                  | ~ r1_lattices(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_lattices)).

fof(f141,plain,(
    r1_lattices(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f140,f48])).

fof(f140,plain,
    ( r1_lattices(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f139,f47])).

fof(f139,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_lattices(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f138,f49])).

fof(f49,plain,(
    r3_lattices(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f138,plain,(
    ! [X0,X1] :
      ( ~ r3_lattices(sK0,X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r1_lattices(sK0,X1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f137,f43])).

fof(f137,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r1_lattices(sK0,X1,X0)
      | v2_struct_0(sK0)
      | ~ r3_lattices(sK0,X1,X0) ) ),
    inference(subsumption_resolution,[],[f136,f46])).

fof(f136,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | r1_lattices(sK0,X1,X0)
      | v2_struct_0(sK0)
      | ~ r3_lattices(sK0,X1,X0) ) ),
    inference(resolution,[],[f135,f44])).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,X1,X2)
      | v2_struct_0(X0)
      | ~ r3_lattices(X0,X1,X2) ) ),
    inference(subsumption_resolution,[],[f134,f55])).

fof(f55,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,X1,X2)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0) ) ),
    inference(subsumption_resolution,[],[f133,f56])).

fof(f56,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f133,plain,(
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
    inference(duplicate_literal_removal,[],[f132])).

fof(f132,plain,(
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
    inference(resolution,[],[f65,f57])).

fof(f57,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f65,plain,(
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
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f258,plain,
    ( k7_lattices(sK0,sK2) != k7_lattices(sK0,k3_lattices(sK0,sK1,sK2))
    | ~ l2_lattices(sK0)
    | ~ v4_lattices(sK0) ),
    inference(subsumption_resolution,[],[f257,f43])).

fof(f257,plain,
    ( k7_lattices(sK0,sK2) != k7_lattices(sK0,k3_lattices(sK0,sK1,sK2))
    | ~ l2_lattices(sK0)
    | ~ v4_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f256,f47])).

fof(f256,plain,
    ( k7_lattices(sK0,sK2) != k7_lattices(sK0,k3_lattices(sK0,sK1,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l2_lattices(sK0)
    | ~ v4_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f254,f48])).

fof(f254,plain,
    ( k7_lattices(sK0,sK2) != k7_lattices(sK0,k3_lattices(sK0,sK1,sK2))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l2_lattices(sK0)
    | ~ v4_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f253,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_lattices)).

fof(f253,plain,(
    k7_lattices(sK0,sK2) != k7_lattices(sK0,k3_lattices(sK0,sK2,sK1)) ),
    inference(subsumption_resolution,[],[f252,f43])).

fof(f252,plain,
    ( k7_lattices(sK0,sK2) != k7_lattices(sK0,k3_lattices(sK0,sK2,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f251,f46])).

fof(f251,plain,
    ( k7_lattices(sK0,sK2) != k7_lattices(sK0,k3_lattices(sK0,sK2,sK1))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f250,f47])).

fof(f250,plain,
    ( k7_lattices(sK0,sK2) != k7_lattices(sK0,k3_lattices(sK0,sK2,sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f249,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_lattices)).

fof(f249,plain,
    ( ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | k7_lattices(sK0,sK2) != k7_lattices(sK0,k3_lattices(sK0,sK2,sK1)) ),
    inference(subsumption_resolution,[],[f248,f43])).

fof(f248,plain,
    ( ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | k7_lattices(sK0,sK2) != k7_lattices(sK0,k3_lattices(sK0,sK2,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f247,f46])).

fof(f247,plain,
    ( ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | k7_lattices(sK0,sK2) != k7_lattices(sK0,k3_lattices(sK0,sK2,sK1))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f246,f48])).

fof(f246,plain,
    ( ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | k7_lattices(sK0,sK2) != k7_lattices(sK0,k3_lattices(sK0,sK2,sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f244,f63])).

fof(f244,plain,
    ( ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | k7_lattices(sK0,sK2) != k7_lattices(sK0,k3_lattices(sK0,sK2,sK1)) ),
    inference(subsumption_resolution,[],[f243,f47])).

fof(f243,plain,
    ( k7_lattices(sK0,sK2) != k7_lattices(sK0,k3_lattices(sK0,sK2,sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f240,f48])).

fof(f240,plain,
    ( k7_lattices(sK0,sK2) != k7_lattices(sK0,k3_lattices(sK0,sK2,sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) ),
    inference(resolution,[],[f239,f191])).

fof(f191,plain,
    ( ~ r1_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))
    | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) ),
    inference(resolution,[],[f190,f50])).

fof(f50,plain,(
    ~ r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) ),
    inference(cnf_transformation,[],[f39])).

fof(f190,plain,(
    ! [X0,X1] :
      ( r3_lattices(sK0,X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_lattices(sK0,X1,X0) ) ),
    inference(subsumption_resolution,[],[f189,f43])).

fof(f189,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r3_lattices(sK0,X1,X0)
      | v2_struct_0(sK0)
      | ~ r1_lattices(sK0,X1,X0) ) ),
    inference(subsumption_resolution,[],[f188,f46])).

fof(f188,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | r3_lattices(sK0,X1,X0)
      | v2_struct_0(sK0)
      | ~ r1_lattices(sK0,X1,X0) ) ),
    inference(resolution,[],[f187,f44])).

fof(f187,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r3_lattices(X0,X1,X2)
      | v2_struct_0(X0)
      | ~ r1_lattices(X0,X1,X2) ) ),
    inference(subsumption_resolution,[],[f186,f55])).

fof(f186,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r3_lattices(X0,X1,X2)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0) ) ),
    inference(subsumption_resolution,[],[f185,f56])).

fof(f185,plain,(
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
    inference(duplicate_literal_removal,[],[f184])).

fof(f184,plain,(
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
    inference(resolution,[],[f66,f57])).

fof(f66,plain,(
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
    inference(cnf_transformation,[],[f42])).

fof(f239,plain,(
    ! [X0,X1] :
      ( r1_lattices(sK0,k7_lattices(sK0,X0),k7_lattices(sK0,X1))
      | k7_lattices(sK0,X0) != k7_lattices(sK0,k3_lattices(sK0,X0,X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f238,f43])).

fof(f238,plain,(
    ! [X0,X1] :
      ( k7_lattices(sK0,X0) != k7_lattices(sK0,k3_lattices(sK0,X0,X1))
      | r1_lattices(sK0,k7_lattices(sK0,X0),k7_lattices(sK0,X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f237,f46])).

fof(f237,plain,(
    ! [X0,X1] :
      ( k7_lattices(sK0,X0) != k7_lattices(sK0,k3_lattices(sK0,X0,X1))
      | r1_lattices(sK0,k7_lattices(sK0,X0),k7_lattices(sK0,X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f236])).

fof(f236,plain,(
    ! [X0,X1] :
      ( k7_lattices(sK0,X0) != k7_lattices(sK0,k3_lattices(sK0,X0,X1))
      | r1_lattices(sK0,k7_lattices(sK0,X0),k7_lattices(sK0,X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f235,f63])).

fof(f235,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
      | k7_lattices(sK0,X0) != k7_lattices(sK0,k3_lattices(sK0,X0,X1))
      | r1_lattices(sK0,k7_lattices(sK0,X0),k7_lattices(sK0,X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f234,f43])).

fof(f234,plain,(
    ! [X0,X1] :
      ( r1_lattices(sK0,k7_lattices(sK0,X0),k7_lattices(sK0,X1))
      | k7_lattices(sK0,X0) != k7_lattices(sK0,k3_lattices(sK0,X0,X1))
      | ~ m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f233,f46])).

fof(f233,plain,(
    ! [X0,X1] :
      ( r1_lattices(sK0,k7_lattices(sK0,X0),k7_lattices(sK0,X1))
      | k7_lattices(sK0,X0) != k7_lattices(sK0,k3_lattices(sK0,X0,X1))
      | ~ m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f232])).

fof(f232,plain,(
    ! [X0,X1] :
      ( r1_lattices(sK0,k7_lattices(sK0,X0),k7_lattices(sK0,X1))
      | k7_lattices(sK0,X0) != k7_lattices(sK0,k3_lattices(sK0,X0,X1))
      | ~ m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f231,f63])).

fof(f231,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k7_lattices(sK0,X1),u1_struct_0(sK0))
      | r1_lattices(sK0,k7_lattices(sK0,X0),k7_lattices(sK0,X1))
      | k7_lattices(sK0,X0) != k7_lattices(sK0,k3_lattices(sK0,X0,X1))
      | ~ m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f230,f46])).

fof(f230,plain,(
    ! [X0,X1] :
      ( r1_lattices(sK0,k7_lattices(sK0,X0),k7_lattices(sK0,X1))
      | ~ m1_subset_1(k7_lattices(sK0,X1),u1_struct_0(sK0))
      | k7_lattices(sK0,X0) != k7_lattices(sK0,k3_lattices(sK0,X0,X1))
      | ~ m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l3_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f229,f43])).

fof(f229,plain,(
    ! [X0,X1] :
      ( r1_lattices(sK0,k7_lattices(sK0,X0),k7_lattices(sK0,X1))
      | ~ m1_subset_1(k7_lattices(sK0,X1),u1_struct_0(sK0))
      | k7_lattices(sK0,X0) != k7_lattices(sK0,k3_lattices(sK0,X0,X1))
      | ~ m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | ~ l3_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f228,f44])).

fof(f228,plain,(
    ! [X0,X1] :
      ( r1_lattices(sK0,k7_lattices(sK0,X0),k7_lattices(sK0,X1))
      | ~ m1_subset_1(k7_lattices(sK0,X1),u1_struct_0(sK0))
      | k7_lattices(sK0,X0) != k7_lattices(sK0,k3_lattices(sK0,X0,X1))
      | ~ m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ l3_lattices(sK0) ) ),
    inference(resolution,[],[f227,f55])).

fof(f227,plain,(
    ! [X0,X1] :
      ( ~ v6_lattices(sK0)
      | r1_lattices(sK0,k7_lattices(sK0,X0),k7_lattices(sK0,X1))
      | ~ m1_subset_1(k7_lattices(sK0,X1),u1_struct_0(sK0))
      | k7_lattices(sK0,X0) != k7_lattices(sK0,k3_lattices(sK0,X0,X1))
      | ~ m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f226,f46])).

fof(f226,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
      | r1_lattices(sK0,k7_lattices(sK0,X0),k7_lattices(sK0,X1))
      | ~ m1_subset_1(k7_lattices(sK0,X1),u1_struct_0(sK0))
      | k7_lattices(sK0,X0) != k7_lattices(sK0,k3_lattices(sK0,X0,X1))
      | ~ v6_lattices(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l3_lattices(sK0) ) ),
    inference(resolution,[],[f225,f51])).

fof(f51,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f225,plain,(
    ! [X0,X1] :
      ( ~ l1_lattices(sK0)
      | ~ m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
      | r1_lattices(sK0,k7_lattices(sK0,X0),k7_lattices(sK0,X1))
      | ~ m1_subset_1(k7_lattices(sK0,X1),u1_struct_0(sK0))
      | k7_lattices(sK0,X0) != k7_lattices(sK0,k3_lattices(sK0,X0,X1))
      | ~ v6_lattices(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(superposition,[],[f131,f224])).

fof(f224,plain,(
    ! [X0,X1] :
      ( k7_lattices(sK0,k3_lattices(sK0,X1,X0)) = k4_lattices(sK0,k7_lattices(sK0,X1),k7_lattices(sK0,X0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f223,f43])).

fof(f223,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k7_lattices(sK0,k3_lattices(sK0,X1,X0)) = k4_lattices(sK0,k7_lattices(sK0,X1),k7_lattices(sK0,X0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f222,f44])).

fof(f222,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k7_lattices(sK0,k3_lattices(sK0,X1,X0)) = k4_lattices(sK0,k7_lattices(sK0,X1),k7_lattices(sK0,X0))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f221,f46])).

fof(f221,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | k7_lattices(sK0,k3_lattices(sK0,X1,X0)) = k4_lattices(sK0,k7_lattices(sK0,X1),k7_lattices(sK0,X0))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f58,f45])).

fof(f45,plain,(
    v17_lattices(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f58,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f131,plain,(
    ! [X0,X1] :
      ( k4_lattices(sK0,X0,X1) != X0
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l1_lattices(sK0)
      | ~ v6_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f130,f43])).

fof(f130,plain,(
    ! [X0,X1] :
      ( k4_lattices(sK0,X0,X1) != X0
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l1_lattices(sK0)
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f129])).

fof(f129,plain,(
    ! [X0,X1] :
      ( k4_lattices(sK0,X0,X1) != X0
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_lattices(sK0)
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f128,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_lattices)).

fof(f128,plain,(
    ! [X0,X1] :
      ( k2_lattices(sK0,X1,X0) != X1
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r1_lattices(sK0,X1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f127,f43])).

fof(f127,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r1_lattices(sK0,X1,X0)
      | v2_struct_0(sK0)
      | k2_lattices(sK0,X1,X0) != X1 ) ),
    inference(subsumption_resolution,[],[f126,f46])).

fof(f126,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | r1_lattices(sK0,X1,X0)
      | v2_struct_0(sK0)
      | k2_lattices(sK0,X1,X0) != X1 ) ),
    inference(resolution,[],[f125,f44])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,X1,X2)
      | v2_struct_0(X0)
      | k2_lattices(X0,X1,X2) != X1 ) ),
    inference(subsumption_resolution,[],[f124,f56])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( k2_lattices(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,X1,X2)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0) ) ),
    inference(duplicate_literal_removal,[],[f123])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( k2_lattices(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,X1,X2)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(resolution,[],[f60,f57])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v9_lattices(X0)
      | k2_lattices(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,X1,X2)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:15:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.45  % (8644)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.20/0.47  % (8652)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.20/0.49  % (8649)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.20/0.49  % (8639)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.49  % (8657)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.20/0.49  % (8657)Refutation not found, incomplete strategy% (8657)------------------------------
% 0.20/0.49  % (8657)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (8636)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.20/0.49  % (8653)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.20/0.49  % (8657)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (8657)Memory used [KB]: 10618
% 0.20/0.49  % (8657)Time elapsed: 0.084 s
% 0.20/0.49  % (8657)------------------------------
% 0.20/0.49  % (8657)------------------------------
% 0.20/0.50  % (8640)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.20/0.50  % (8643)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.20/0.50  % (8637)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.50  % (8647)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.20/0.50  % (8637)Refutation not found, incomplete strategy% (8637)------------------------------
% 0.20/0.50  % (8637)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (8637)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (8637)Memory used [KB]: 10618
% 0.20/0.50  % (8637)Time elapsed: 0.090 s
% 0.20/0.50  % (8637)------------------------------
% 0.20/0.50  % (8637)------------------------------
% 0.20/0.50  % (8656)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.20/0.50  % (8638)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.20/0.50  % (8655)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.20/0.50  % (8642)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.20/0.51  % (8635)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.20/0.51  % (8645)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.20/0.51  % (8648)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.20/0.51  % (8641)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.52  % (8654)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.20/0.52  % (8650)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.20/0.52  % (8634)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.20/0.52  % (8653)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f266,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(subsumption_resolution,[],[f265,f46])).
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    l3_lattices(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f39])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    ((~r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) & r3_lattices(sK0,sK1,sK2) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l3_lattices(sK0) & v17_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f38,f37,f36])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (? [X2] : (~r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) & r3_lattices(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (~r3_lattices(sK0,k7_lattices(sK0,X2),k7_lattices(sK0,X1)) & r3_lattices(sK0,X1,X2) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) & l3_lattices(sK0) & v17_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    ? [X1] : (? [X2] : (~r3_lattices(sK0,k7_lattices(sK0,X2),k7_lattices(sK0,X1)) & r3_lattices(sK0,X1,X2) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (~r3_lattices(sK0,k7_lattices(sK0,X2),k7_lattices(sK0,sK1)) & r3_lattices(sK0,sK1,X2) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    ? [X2] : (~r3_lattices(sK0,k7_lattices(sK0,X2),k7_lattices(sK0,sK1)) & r3_lattices(sK0,sK1,X2) & m1_subset_1(X2,u1_struct_0(sK0))) => (~r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) & r3_lattices(sK0,sK1,sK2) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (? [X2] : (~r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) & r3_lattices(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (? [X2] : ((~r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) & r3_lattices(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,negated_conjecture,(
% 0.20/0.52    ~! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_lattices(X0,X1,X2) => r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))))))),
% 0.20/0.52    inference(negated_conjecture,[],[f11])).
% 0.20/0.52  fof(f11,conjecture,(
% 0.20/0.52    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_lattices(X0,X1,X2) => r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_lattices)).
% 0.20/0.52  fof(f265,plain,(
% 0.20/0.52    ~l3_lattices(sK0)),
% 0.20/0.52    inference(subsumption_resolution,[],[f264,f43])).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    ~v2_struct_0(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f39])).
% 0.20/0.52  fof(f264,plain,(
% 0.20/0.52    v2_struct_0(sK0) | ~l3_lattices(sK0)),
% 0.20/0.52    inference(subsumption_resolution,[],[f263,f44])).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    v10_lattices(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f39])).
% 0.20/0.52  fof(f263,plain,(
% 0.20/0.52    ~v10_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0)),
% 0.20/0.52    inference(resolution,[],[f262,f54])).
% 0.20/0.52  fof(f54,plain,(
% 0.20/0.52    ( ! [X0] : (v4_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 0.20/0.52    inference(flattening,[],[f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f14])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.20/0.52    inference(pure_predicate_removal,[],[f13])).
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.20/0.52    inference(pure_predicate_removal,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).
% 0.20/0.52  fof(f262,plain,(
% 0.20/0.52    ~v4_lattices(sK0)),
% 0.20/0.52    inference(subsumption_resolution,[],[f261,f46])).
% 0.20/0.52  fof(f261,plain,(
% 0.20/0.52    ~v4_lattices(sK0) | ~l3_lattices(sK0)),
% 0.20/0.52    inference(resolution,[],[f260,f52])).
% 0.20/0.52  fof(f52,plain,(
% 0.20/0.52    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).
% 0.20/0.52  fof(f260,plain,(
% 0.20/0.52    ~l2_lattices(sK0) | ~v4_lattices(sK0)),
% 0.20/0.52    inference(trivial_inequality_removal,[],[f259])).
% 0.20/0.52  fof(f259,plain,(
% 0.20/0.52    k7_lattices(sK0,sK2) != k7_lattices(sK0,sK2) | ~l2_lattices(sK0) | ~v4_lattices(sK0)),
% 0.20/0.52    inference(forward_demodulation,[],[f258,f163])).
% 0.20/0.52  fof(f163,plain,(
% 0.20/0.52    sK2 = k3_lattices(sK0,sK1,sK2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f162,f47])).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.52    inference(cnf_transformation,[],[f39])).
% 0.20/0.52  fof(f162,plain,(
% 0.20/0.52    sK2 = k3_lattices(sK0,sK1,sK2) | ~m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.52    inference(subsumption_resolution,[],[f158,f48])).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.20/0.52    inference(cnf_transformation,[],[f39])).
% 0.20/0.52  fof(f158,plain,(
% 0.20/0.52    sK2 = k3_lattices(sK0,sK1,sK2) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.52    inference(superposition,[],[f157,f74])).
% 0.20/0.52  fof(f74,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k3_lattices(sK0,X0,X1) = k1_lattices(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f73,f46])).
% 0.20/0.52  fof(f73,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k3_lattices(sK0,X0,X1) = k1_lattices(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f72,f43])).
% 0.20/0.52  fof(f72,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k3_lattices(sK0,X0,X1) = k1_lattices(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.20/0.52    inference(resolution,[],[f71,f44])).
% 0.20/0.52  fof(f71,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~v10_lattices(X1) | k3_lattices(X1,X0,X2) = k1_lattices(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X1)) | v2_struct_0(X1) | ~l3_lattices(X1) | ~m1_subset_1(X0,u1_struct_0(X1))) )),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f70])).
% 0.20/0.52  fof(f70,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | k3_lattices(X1,X0,X2) = k1_lattices(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X1)) | v2_struct_0(X1) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X1)) )),
% 0.20/0.52    inference(resolution,[],[f69,f54])).
% 0.20/0.52  fof(f69,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~v4_lattices(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | k3_lattices(X1,X2,X0) = k1_lattices(X1,X2,X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | v2_struct_0(X1) | ~l3_lattices(X1)) )),
% 0.20/0.52    inference(resolution,[],[f67,f52])).
% 0.20/0.52  fof(f67,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~l2_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f33])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f32])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_lattices)).
% 0.20/0.52  fof(f157,plain,(
% 0.20/0.52    sK2 = k1_lattices(sK0,sK1,sK2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f156,f46])).
% 0.20/0.52  fof(f156,plain,(
% 0.20/0.52    sK2 = k1_lattices(sK0,sK1,sK2) | ~l3_lattices(sK0)),
% 0.20/0.52    inference(resolution,[],[f148,f52])).
% 0.20/0.52  fof(f148,plain,(
% 0.20/0.52    ~l2_lattices(sK0) | sK2 = k1_lattices(sK0,sK1,sK2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f147,f43])).
% 0.20/0.52  fof(f147,plain,(
% 0.20/0.52    sK2 = k1_lattices(sK0,sK1,sK2) | ~l2_lattices(sK0) | v2_struct_0(sK0)),
% 0.20/0.52    inference(subsumption_resolution,[],[f146,f47])).
% 0.20/0.52  fof(f146,plain,(
% 0.20/0.52    sK2 = k1_lattices(sK0,sK1,sK2) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l2_lattices(sK0) | v2_struct_0(sK0)),
% 0.20/0.52    inference(subsumption_resolution,[],[f143,f48])).
% 0.20/0.52  fof(f143,plain,(
% 0.20/0.52    sK2 = k1_lattices(sK0,sK1,sK2) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l2_lattices(sK0) | v2_struct_0(sK0)),
% 0.20/0.52    inference(resolution,[],[f141,f61])).
% 0.20/0.52  fof(f61,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r1_lattices(X0,X1,X2) | k1_lattices(X0,X1,X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f41])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k1_lattices(X0,X1,X2) != X2) & (k1_lattices(X0,X1,X2) = X2 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(nnf_transformation,[],[f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_lattices)).
% 0.20/0.52  fof(f141,plain,(
% 0.20/0.52    r1_lattices(sK0,sK1,sK2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f140,f48])).
% 0.20/0.52  fof(f140,plain,(
% 0.20/0.52    r1_lattices(sK0,sK1,sK2) | ~m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.20/0.52    inference(subsumption_resolution,[],[f139,f47])).
% 0.20/0.52  fof(f139,plain,(
% 0.20/0.52    ~m1_subset_1(sK1,u1_struct_0(sK0)) | r1_lattices(sK0,sK1,sK2) | ~m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.20/0.52    inference(resolution,[],[f138,f49])).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    r3_lattices(sK0,sK1,sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f39])).
% 0.20/0.52  fof(f138,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r3_lattices(sK0,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_lattices(sK0,X1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f137,f43])).
% 0.20/0.52  fof(f137,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_lattices(sK0,X1,X0) | v2_struct_0(sK0) | ~r3_lattices(sK0,X1,X0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f136,f46])).
% 0.20/0.52  fof(f136,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | r1_lattices(sK0,X1,X0) | v2_struct_0(sK0) | ~r3_lattices(sK0,X1,X0)) )),
% 0.20/0.52    inference(resolution,[],[f135,f44])).
% 0.20/0.52  fof(f135,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~v10_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r1_lattices(X0,X1,X2) | v2_struct_0(X0) | ~r3_lattices(X0,X1,X2)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f134,f55])).
% 0.20/0.52  fof(f55,plain,(
% 0.20/0.52    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f19])).
% 0.20/0.52  fof(f134,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r1_lattices(X0,X1,X2) | ~v6_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f133,f56])).
% 0.20/0.52  fof(f56,plain,(
% 0.20/0.52    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f19])).
% 0.20/0.52  fof(f133,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r1_lattices(X0,X1,X2) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0)) )),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f132])).
% 0.20/0.52  fof(f132,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r1_lattices(X0,X1,X2) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.20/0.52    inference(resolution,[],[f65,f57])).
% 0.20/0.52  fof(f57,plain,(
% 0.20/0.52    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f19])).
% 0.20/0.52  fof(f65,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~v9_lattices(X0) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r1_lattices(X0,X1,X2) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f42])).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(nnf_transformation,[],[f31])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f30])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_lattices)).
% 0.20/0.52  fof(f258,plain,(
% 0.20/0.52    k7_lattices(sK0,sK2) != k7_lattices(sK0,k3_lattices(sK0,sK1,sK2)) | ~l2_lattices(sK0) | ~v4_lattices(sK0)),
% 0.20/0.52    inference(subsumption_resolution,[],[f257,f43])).
% 0.20/0.52  fof(f257,plain,(
% 0.20/0.52    k7_lattices(sK0,sK2) != k7_lattices(sK0,k3_lattices(sK0,sK1,sK2)) | ~l2_lattices(sK0) | ~v4_lattices(sK0) | v2_struct_0(sK0)),
% 0.20/0.52    inference(subsumption_resolution,[],[f256,f47])).
% 0.20/0.52  fof(f256,plain,(
% 0.20/0.52    k7_lattices(sK0,sK2) != k7_lattices(sK0,k3_lattices(sK0,sK1,sK2)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l2_lattices(sK0) | ~v4_lattices(sK0) | v2_struct_0(sK0)),
% 0.20/0.52    inference(subsumption_resolution,[],[f254,f48])).
% 0.20/0.52  fof(f254,plain,(
% 0.20/0.52    k7_lattices(sK0,sK2) != k7_lattices(sK0,k3_lattices(sK0,sK1,sK2)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l2_lattices(sK0) | ~v4_lattices(sK0) | v2_struct_0(sK0)),
% 0.20/0.52    inference(superposition,[],[f253,f68])).
% 0.20/0.52  fof(f68,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f35])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f34])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_lattices)).
% 0.20/0.52  fof(f253,plain,(
% 0.20/0.52    k7_lattices(sK0,sK2) != k7_lattices(sK0,k3_lattices(sK0,sK2,sK1))),
% 0.20/0.52    inference(subsumption_resolution,[],[f252,f43])).
% 0.20/0.52  fof(f252,plain,(
% 0.20/0.52    k7_lattices(sK0,sK2) != k7_lattices(sK0,k3_lattices(sK0,sK2,sK1)) | v2_struct_0(sK0)),
% 0.20/0.52    inference(subsumption_resolution,[],[f251,f46])).
% 0.20/0.52  fof(f251,plain,(
% 0.20/0.52    k7_lattices(sK0,sK2) != k7_lattices(sK0,k3_lattices(sK0,sK2,sK1)) | ~l3_lattices(sK0) | v2_struct_0(sK0)),
% 0.20/0.52    inference(subsumption_resolution,[],[f250,f47])).
% 0.20/0.52  fof(f250,plain,(
% 0.20/0.52    k7_lattices(sK0,sK2) != k7_lattices(sK0,k3_lattices(sK0,sK2,sK1)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0)),
% 0.20/0.52    inference(resolution,[],[f249,f63])).
% 0.20/0.52  fof(f63,plain,(
% 0.20/0.52    ( ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f27])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_lattices)).
% 0.20/0.52  fof(f249,plain,(
% 0.20/0.52    ~m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) | k7_lattices(sK0,sK2) != k7_lattices(sK0,k3_lattices(sK0,sK2,sK1))),
% 0.20/0.52    inference(subsumption_resolution,[],[f248,f43])).
% 0.20/0.52  fof(f248,plain,(
% 0.20/0.52    ~m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) | k7_lattices(sK0,sK2) != k7_lattices(sK0,k3_lattices(sK0,sK2,sK1)) | v2_struct_0(sK0)),
% 0.20/0.52    inference(subsumption_resolution,[],[f247,f46])).
% 0.20/0.52  fof(f247,plain,(
% 0.20/0.52    ~m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) | k7_lattices(sK0,sK2) != k7_lattices(sK0,k3_lattices(sK0,sK2,sK1)) | ~l3_lattices(sK0) | v2_struct_0(sK0)),
% 0.20/0.52    inference(subsumption_resolution,[],[f246,f48])).
% 0.20/0.52  fof(f246,plain,(
% 0.20/0.52    ~m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) | k7_lattices(sK0,sK2) != k7_lattices(sK0,k3_lattices(sK0,sK2,sK1)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0)),
% 0.20/0.52    inference(resolution,[],[f244,f63])).
% 0.20/0.52  fof(f244,plain,(
% 0.20/0.52    ~m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) | ~m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) | k7_lattices(sK0,sK2) != k7_lattices(sK0,k3_lattices(sK0,sK2,sK1))),
% 0.20/0.52    inference(subsumption_resolution,[],[f243,f47])).
% 0.20/0.52  fof(f243,plain,(
% 0.20/0.52    k7_lattices(sK0,sK2) != k7_lattices(sK0,k3_lattices(sK0,sK2,sK1)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) | ~m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))),
% 0.20/0.52    inference(subsumption_resolution,[],[f240,f48])).
% 0.20/0.52  fof(f240,plain,(
% 0.20/0.52    k7_lattices(sK0,sK2) != k7_lattices(sK0,k3_lattices(sK0,sK2,sK1)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) | ~m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))),
% 0.20/0.52    inference(resolution,[],[f239,f191])).
% 0.20/0.52  fof(f191,plain,(
% 0.20/0.52    ~r1_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) | ~m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) | ~m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))),
% 0.20/0.52    inference(resolution,[],[f190,f50])).
% 0.20/0.52  fof(f50,plain,(
% 0.20/0.52    ~r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))),
% 0.20/0.52    inference(cnf_transformation,[],[f39])).
% 0.20/0.52  fof(f190,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r3_lattices(sK0,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_lattices(sK0,X1,X0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f189,f43])).
% 0.20/0.52  fof(f189,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r3_lattices(sK0,X1,X0) | v2_struct_0(sK0) | ~r1_lattices(sK0,X1,X0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f188,f46])).
% 0.20/0.52  fof(f188,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | r3_lattices(sK0,X1,X0) | v2_struct_0(sK0) | ~r1_lattices(sK0,X1,X0)) )),
% 0.20/0.52    inference(resolution,[],[f187,f44])).
% 0.20/0.52  fof(f187,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~v10_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r3_lattices(X0,X1,X2) | v2_struct_0(X0) | ~r1_lattices(X0,X1,X2)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f186,f55])).
% 0.20/0.52  fof(f186,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r3_lattices(X0,X1,X2) | ~v6_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f185,f56])).
% 0.20/0.52  fof(f185,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r3_lattices(X0,X1,X2) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0)) )),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f184])).
% 0.20/0.52  fof(f184,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r3_lattices(X0,X1,X2) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.20/0.52    inference(resolution,[],[f66,f57])).
% 0.20/0.52  fof(f66,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~v9_lattices(X0) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r3_lattices(X0,X1,X2) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f42])).
% 0.20/0.52  fof(f239,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_lattices(sK0,k7_lattices(sK0,X0),k7_lattices(sK0,X1)) | k7_lattices(sK0,X0) != k7_lattices(sK0,k3_lattices(sK0,X0,X1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f238,f43])).
% 0.20/0.52  fof(f238,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k7_lattices(sK0,X0) != k7_lattices(sK0,k3_lattices(sK0,X0,X1)) | r1_lattices(sK0,k7_lattices(sK0,X0),k7_lattices(sK0,X1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f237,f46])).
% 0.20/0.52  fof(f237,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k7_lattices(sK0,X0) != k7_lattices(sK0,k3_lattices(sK0,X0,X1)) | r1_lattices(sK0,k7_lattices(sK0,X0),k7_lattices(sK0,X1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f236])).
% 0.20/0.52  fof(f236,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k7_lattices(sK0,X0) != k7_lattices(sK0,k3_lattices(sK0,X0,X1)) | r1_lattices(sK0,k7_lattices(sK0,X0),k7_lattices(sK0,X1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.52    inference(resolution,[],[f235,f63])).
% 0.20/0.52  fof(f235,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0)) | k7_lattices(sK0,X0) != k7_lattices(sK0,k3_lattices(sK0,X0,X1)) | r1_lattices(sK0,k7_lattices(sK0,X0),k7_lattices(sK0,X1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f234,f43])).
% 0.20/0.52  fof(f234,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_lattices(sK0,k7_lattices(sK0,X0),k7_lattices(sK0,X1)) | k7_lattices(sK0,X0) != k7_lattices(sK0,k3_lattices(sK0,X0,X1)) | ~m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f233,f46])).
% 0.20/0.52  fof(f233,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_lattices(sK0,k7_lattices(sK0,X0),k7_lattices(sK0,X1)) | k7_lattices(sK0,X0) != k7_lattices(sK0,k3_lattices(sK0,X0,X1)) | ~m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f232])).
% 0.20/0.52  fof(f232,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_lattices(sK0,k7_lattices(sK0,X0),k7_lattices(sK0,X1)) | k7_lattices(sK0,X0) != k7_lattices(sK0,k3_lattices(sK0,X0,X1)) | ~m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.52    inference(resolution,[],[f231,f63])).
% 0.20/0.52  fof(f231,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(k7_lattices(sK0,X1),u1_struct_0(sK0)) | r1_lattices(sK0,k7_lattices(sK0,X0),k7_lattices(sK0,X1)) | k7_lattices(sK0,X0) != k7_lattices(sK0,k3_lattices(sK0,X0,X1)) | ~m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f230,f46])).
% 0.20/0.52  fof(f230,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_lattices(sK0,k7_lattices(sK0,X0),k7_lattices(sK0,X1)) | ~m1_subset_1(k7_lattices(sK0,X1),u1_struct_0(sK0)) | k7_lattices(sK0,X0) != k7_lattices(sK0,k3_lattices(sK0,X0,X1)) | ~m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l3_lattices(sK0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f229,f43])).
% 0.20/0.52  fof(f229,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_lattices(sK0,k7_lattices(sK0,X0),k7_lattices(sK0,X1)) | ~m1_subset_1(k7_lattices(sK0,X1),u1_struct_0(sK0)) | k7_lattices(sK0,X0) != k7_lattices(sK0,k3_lattices(sK0,X0,X1)) | ~m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~l3_lattices(sK0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f228,f44])).
% 0.20/0.52  fof(f228,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_lattices(sK0,k7_lattices(sK0,X0),k7_lattices(sK0,X1)) | ~m1_subset_1(k7_lattices(sK0,X1),u1_struct_0(sK0)) | k7_lattices(sK0,X0) != k7_lattices(sK0,k3_lattices(sK0,X0,X1)) | ~m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v10_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0)) )),
% 0.20/0.52    inference(resolution,[],[f227,f55])).
% 0.20/0.52  fof(f227,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v6_lattices(sK0) | r1_lattices(sK0,k7_lattices(sK0,X0),k7_lattices(sK0,X1)) | ~m1_subset_1(k7_lattices(sK0,X1),u1_struct_0(sK0)) | k7_lattices(sK0,X0) != k7_lattices(sK0,k3_lattices(sK0,X0,X1)) | ~m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f226,f46])).
% 0.20/0.52  fof(f226,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0)) | r1_lattices(sK0,k7_lattices(sK0,X0),k7_lattices(sK0,X1)) | ~m1_subset_1(k7_lattices(sK0,X1),u1_struct_0(sK0)) | k7_lattices(sK0,X0) != k7_lattices(sK0,k3_lattices(sK0,X0,X1)) | ~v6_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l3_lattices(sK0)) )),
% 0.20/0.52    inference(resolution,[],[f225,f51])).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f17])).
% 0.20/0.52  fof(f225,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~l1_lattices(sK0) | ~m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0)) | r1_lattices(sK0,k7_lattices(sK0,X0),k7_lattices(sK0,X1)) | ~m1_subset_1(k7_lattices(sK0,X1),u1_struct_0(sK0)) | k7_lattices(sK0,X0) != k7_lattices(sK0,k3_lattices(sK0,X0,X1)) | ~v6_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) )),
% 0.20/0.52    inference(superposition,[],[f131,f224])).
% 0.20/0.52  fof(f224,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k7_lattices(sK0,k3_lattices(sK0,X1,X0)) = k4_lattices(sK0,k7_lattices(sK0,X1),k7_lattices(sK0,X0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f223,f43])).
% 0.20/0.52  fof(f223,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k7_lattices(sK0,k3_lattices(sK0,X1,X0)) = k4_lattices(sK0,k7_lattices(sK0,X1),k7_lattices(sK0,X0)) | v2_struct_0(sK0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f222,f44])).
% 0.20/0.52  fof(f222,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k7_lattices(sK0,k3_lattices(sK0,X1,X0)) = k4_lattices(sK0,k7_lattices(sK0,X1),k7_lattices(sK0,X0)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f221,f46])).
% 0.20/0.52  fof(f221,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | k7_lattices(sK0,k3_lattices(sK0,X1,X0)) = k4_lattices(sK0,k7_lattices(sK0,X1),k7_lattices(sK0,X0)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.52    inference(resolution,[],[f58,f45])).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    v17_lattices(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f39])).
% 0.20/0.52  fof(f58,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~v17_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f21])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : (k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f20])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : (k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,axiom,(
% 0.20/0.52    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_lattices)).
% 0.20/0.52  fof(f131,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k4_lattices(sK0,X0,X1) != X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_lattices(sK0) | ~v6_lattices(sK0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f130,f43])).
% 0.20/0.52  fof(f130,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k4_lattices(sK0,X0,X1) != X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f129])).
% 0.20/0.52  fof(f129,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k4_lattices(sK0,X0,X1) != X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.52    inference(superposition,[],[f128,f64])).
% 0.20/0.52  fof(f64,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f29])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f28])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_lattices)).
% 0.20/0.52  fof(f128,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k2_lattices(sK0,X1,X0) != X1 | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_lattices(sK0,X1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f127,f43])).
% 0.20/0.52  fof(f127,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_lattices(sK0,X1,X0) | v2_struct_0(sK0) | k2_lattices(sK0,X1,X0) != X1) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f126,f46])).
% 0.20/0.52  fof(f126,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | r1_lattices(sK0,X1,X0) | v2_struct_0(sK0) | k2_lattices(sK0,X1,X0) != X1) )),
% 0.20/0.52    inference(resolution,[],[f125,f44])).
% 0.20/0.52  fof(f125,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~v10_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r1_lattices(X0,X1,X2) | v2_struct_0(X0) | k2_lattices(X0,X1,X2) != X1) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f124,f56])).
% 0.20/0.52  fof(f124,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k2_lattices(X0,X1,X2) != X1 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r1_lattices(X0,X1,X2) | ~v8_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0)) )),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f123])).
% 0.20/0.52  fof(f123,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k2_lattices(X0,X1,X2) != X1 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r1_lattices(X0,X1,X2) | ~v8_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.20/0.52    inference(resolution,[],[f60,f57])).
% 0.20/0.52  fof(f60,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~v9_lattices(X0) | k2_lattices(X0,X1,X2) != X1 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r1_lattices(X0,X1,X2) | ~v8_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f40])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) != X1) & (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(nnf_transformation,[],[f23])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f22])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,axiom,(
% 0.20/0.52    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_lattices)).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (8653)------------------------------
% 0.20/0.52  % (8653)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (8653)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (8653)Memory used [KB]: 6268
% 0.20/0.52  % (8653)Time elapsed: 0.124 s
% 0.20/0.52  % (8653)------------------------------
% 0.20/0.52  % (8653)------------------------------
% 0.20/0.53  % (8633)Success in time 0.174 s
%------------------------------------------------------------------------------
