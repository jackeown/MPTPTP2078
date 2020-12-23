%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:44 EST 2020

% Result     : Theorem 1.59s
% Output     : Refutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 662 expanded)
%              Number of leaves         :   14 ( 227 expanded)
%              Depth                    :   42
%              Number of atoms          :  762 (4800 expanded)
%              Number of equality atoms :   91 (  91 expanded)
%              Maximal formula depth    :   15 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f259,plain,(
    $false ),
    inference(subsumption_resolution,[],[f258,f220])).

fof(f220,plain,(
    k7_lattices(sK0,sK1) != k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f219,f46])).

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

% (31826)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
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

fof(f219,plain,
    ( k7_lattices(sK0,sK1) != k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2))
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f218,f43])).

fof(f43,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f218,plain,
    ( k7_lattices(sK0,sK1) != k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2))
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f217,f44])).

fof(f44,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f217,plain,
    ( k7_lattices(sK0,sK1) != k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2))
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f216,f54])).

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

fof(f216,plain,
    ( ~ v4_lattices(sK0)
    | k7_lattices(sK0,sK1) != k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f215,f46])).

fof(f215,plain,
    ( k7_lattices(sK0,sK1) != k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2))
    | ~ v4_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f214,f52])).

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

fof(f214,plain,
    ( ~ l2_lattices(sK0)
    | k7_lattices(sK0,sK1) != k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2))
    | ~ v4_lattices(sK0) ),
    inference(subsumption_resolution,[],[f213,f43])).

fof(f213,plain,
    ( k7_lattices(sK0,sK1) != k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2))
    | ~ l2_lattices(sK0)
    | ~ v4_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f212,f46])).

fof(f212,plain,
    ( k7_lattices(sK0,sK1) != k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2))
    | ~ l2_lattices(sK0)
    | ~ v4_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f211,f47])).

fof(f47,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f39])).

fof(f211,plain,
    ( k7_lattices(sK0,sK1) != k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2))
    | ~ l2_lattices(sK0)
    | ~ v4_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f210,f63])).

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

fof(f210,plain,
    ( ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | k7_lattices(sK0,sK1) != k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2))
    | ~ l2_lattices(sK0)
    | ~ v4_lattices(sK0) ),
    inference(subsumption_resolution,[],[f209,f43])).

fof(f209,plain,
    ( k7_lattices(sK0,sK1) != k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2))
    | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ l2_lattices(sK0)
    | ~ v4_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f208,f46])).

fof(f208,plain,
    ( k7_lattices(sK0,sK1) != k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2))
    | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ l2_lattices(sK0)
    | ~ v4_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f207,f48])).

fof(f48,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f39])).

fof(f207,plain,
    ( k7_lattices(sK0,sK1) != k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2))
    | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ l2_lattices(sK0)
    | ~ v4_lattices(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f206,f63])).

fof(f206,plain,
    ( ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | k7_lattices(sK0,sK1) != k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2))
    | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ l2_lattices(sK0)
    | ~ v4_lattices(sK0) ),
    inference(subsumption_resolution,[],[f204,f43])).

fof(f204,plain,
    ( k7_lattices(sK0,sK1) != k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2))
    | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ l2_lattices(sK0)
    | ~ v4_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f203,f68])).

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

fof(f203,plain,(
    k7_lattices(sK0,sK1) != k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f202,f43])).

fof(f202,plain,
    ( k7_lattices(sK0,sK1) != k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f201,f46])).

fof(f201,plain,
    ( k7_lattices(sK0,sK1) != k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f200,f47])).

fof(f200,plain,
    ( k7_lattices(sK0,sK1) != k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f199,f63])).

fof(f199,plain,
    ( ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | k7_lattices(sK0,sK1) != k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f198,f43])).

fof(f198,plain,
    ( ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | k7_lattices(sK0,sK1) != k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f197,f46])).

fof(f197,plain,
    ( ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | k7_lattices(sK0,sK1) != k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f196,f48])).

fof(f196,plain,
    ( ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | k7_lattices(sK0,sK1) != k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f195,f63])).

fof(f195,plain,
    ( ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | k7_lattices(sK0,sK1) != k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) ),
    inference(duplicate_literal_removal,[],[f194])).

fof(f194,plain,
    ( ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | k7_lattices(sK0,sK1) != k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) ),
    inference(resolution,[],[f191,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k3_lattices(sK0,X0,X1) != X1 ) ),
    inference(subsumption_resolution,[],[f78,f46])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k3_lattices(sK0,X0,X1) != X1
      | ~ l3_lattices(sK0) ) ),
    inference(resolution,[],[f77,f52])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ l2_lattices(sK0)
      | r1_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k3_lattices(sK0,X0,X1) != X1 ) ),
    inference(subsumption_resolution,[],[f76,f43])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k3_lattices(sK0,X0,X1) != X1
      | r1_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l2_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k3_lattices(sK0,X0,X1) != X1
      | r1_lattices(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l2_lattices(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(superposition,[],[f62,f74])).

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

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k1_lattices(X0,X1,X2) != X2
      | r1_lattices(X0,X1,X2)
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

fof(f55,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f19])).

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

fof(f56,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f19])).

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

fof(f57,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f19])).

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

fof(f258,plain,(
    k7_lattices(sK0,sK1) = k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) ),
    inference(forward_demodulation,[],[f255,f181])).

fof(f181,plain,(
    sK1 = k4_lattices(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f180,f46])).

fof(f180,plain,
    ( sK1 = k4_lattices(sK0,sK1,sK2)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f179,f43])).

fof(f179,plain,
    ( sK1 = k4_lattices(sK0,sK1,sK2)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f178,f44])).

fof(f178,plain,
    ( sK1 = k4_lattices(sK0,sK1,sK2)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f177,f55])).

fof(f177,plain,
    ( ~ v6_lattices(sK0)
    | sK1 = k4_lattices(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f176,f46])).

fof(f176,plain,
    ( sK1 = k4_lattices(sK0,sK1,sK2)
    | ~ v6_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f155,f51])).

fof(f51,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f155,plain,
    ( ~ l1_lattices(sK0)
    | sK1 = k4_lattices(sK0,sK1,sK2)
    | ~ v6_lattices(sK0) ),
    inference(subsumption_resolution,[],[f154,f43])).

fof(f154,plain,
    ( sK1 = k4_lattices(sK0,sK1,sK2)
    | ~ l1_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f153,f47])).

fof(f153,plain,
    ( sK1 = k4_lattices(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f149,f48])).

fof(f149,plain,
    ( sK1 = k4_lattices(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f145,f64])).

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

% (31810)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
fof(f145,plain,(
    sK1 = k2_lattices(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f144,f48])).

fof(f144,plain,
    ( sK1 = k2_lattices(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f142,f47])).

fof(f142,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | sK1 = k2_lattices(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f141,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ r1_lattices(sK0,X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k2_lattices(sK0,X1,X0) = X1
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f104,f43])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k2_lattices(sK0,X1,X0) = X1
      | v2_struct_0(sK0)
      | ~ r1_lattices(sK0,X1,X0) ) ),
    inference(subsumption_resolution,[],[f103,f46])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | k2_lattices(sK0,X1,X0) = X1
      | v2_struct_0(sK0)
      | ~ r1_lattices(sK0,X1,X0) ) ),
    inference(resolution,[],[f102,f44])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | k2_lattices(X0,X1,X2) = X1
      | v2_struct_0(X0)
      | ~ r1_lattices(X0,X1,X2) ) ),
    inference(subsumption_resolution,[],[f101,f56])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | k2_lattices(X0,X1,X2) = X1
      | ~ v8_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0) ) ),
    inference(duplicate_literal_removal,[],[f100])).

fof(f100,plain,(
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
    inference(resolution,[],[f59,f57])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ v9_lattices(X0)
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | k2_lattices(X0,X1,X2) = X1
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

fof(f255,plain,(
    k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) = k7_lattices(sK0,k4_lattices(sK0,sK1,sK2)) ),
    inference(resolution,[],[f226,f47])).

fof(f226,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k7_lattices(sK0,k4_lattices(sK0,X1,sK2)) = k3_lattices(sK0,k7_lattices(sK0,X1),k7_lattices(sK0,sK2)) ) ),
    inference(resolution,[],[f224,f48])).

fof(f224,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k7_lattices(sK0,k4_lattices(sK0,X1,X0)) = k3_lattices(sK0,k7_lattices(sK0,X1),k7_lattices(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f223,f43])).

fof(f223,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k7_lattices(sK0,k4_lattices(sK0,X1,X0)) = k3_lattices(sK0,k7_lattices(sK0,X1),k7_lattices(sK0,X0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f222,f44])).

fof(f222,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k7_lattices(sK0,k4_lattices(sK0,X1,X0)) = k3_lattices(sK0,k7_lattices(sK0,X1),k7_lattices(sK0,X0))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f221,f46])).

fof(f221,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | k7_lattices(sK0,k4_lattices(sK0,X1,X0)) = k3_lattices(sK0,k7_lattices(sK0,X1),k7_lattices(sK0,X0))
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
      | k7_lattices(X0,k4_lattices(X0,X1,X2)) = k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2))
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k7_lattices(X0,k4_lattices(X0,X1,X2)) = k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2))
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
              ( k7_lattices(X0,k4_lattices(X0,X1,X2)) = k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2))
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
             => k7_lattices(X0,k4_lattices(X0,X1,X2)) = k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_lattices)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:32:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (31814)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.52  % (31822)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.22/0.55  % (31824)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.22/0.55  % (31829)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 1.44/0.56  % (31816)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 1.44/0.56  % (31819)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 1.44/0.56  % (31821)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 1.44/0.56  % (31817)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 1.44/0.56  % (31808)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 1.44/0.56  % (31815)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 1.44/0.56  % (31823)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 1.44/0.56  % (31806)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 1.44/0.56  % (31813)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.44/0.56  % (31807)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 1.44/0.56  % (31809)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 1.44/0.56  % (31811)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 1.44/0.57  % (31809)Refutation not found, incomplete strategy% (31809)------------------------------
% 1.44/0.57  % (31809)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.57  % (31809)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.57  
% 1.44/0.57  % (31809)Memory used [KB]: 10618
% 1.44/0.57  % (31809)Time elapsed: 0.125 s
% 1.44/0.57  % (31809)------------------------------
% 1.44/0.57  % (31809)------------------------------
% 1.59/0.57  % (31825)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 1.59/0.57  % (31829)Refutation not found, incomplete strategy% (31829)------------------------------
% 1.59/0.57  % (31829)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.57  % (31829)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.57  
% 1.59/0.57  % (31829)Memory used [KB]: 10618
% 1.59/0.57  % (31829)Time elapsed: 0.130 s
% 1.59/0.57  % (31829)------------------------------
% 1.59/0.57  % (31829)------------------------------
% 1.59/0.57  % (31818)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 1.59/0.57  % (31820)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 1.59/0.58  % (31827)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 1.59/0.58  % (31828)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 1.59/0.58  % (31825)Refutation found. Thanks to Tanya!
% 1.59/0.58  % SZS status Theorem for theBenchmark
% 1.59/0.58  % SZS output start Proof for theBenchmark
% 1.59/0.58  fof(f259,plain,(
% 1.59/0.58    $false),
% 1.59/0.58    inference(subsumption_resolution,[],[f258,f220])).
% 1.59/0.58  fof(f220,plain,(
% 1.59/0.58    k7_lattices(sK0,sK1) != k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2))),
% 1.59/0.58    inference(subsumption_resolution,[],[f219,f46])).
% 1.59/0.58  fof(f46,plain,(
% 1.59/0.58    l3_lattices(sK0)),
% 1.59/0.58    inference(cnf_transformation,[],[f39])).
% 1.59/0.58  fof(f39,plain,(
% 1.59/0.58    ((~r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) & r3_lattices(sK0,sK1,sK2) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l3_lattices(sK0) & v17_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0)),
% 1.59/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f38,f37,f36])).
% 1.59/0.58  fof(f36,plain,(
% 1.59/0.58    ? [X0] : (? [X1] : (? [X2] : (~r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) & r3_lattices(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (~r3_lattices(sK0,k7_lattices(sK0,X2),k7_lattices(sK0,X1)) & r3_lattices(sK0,X1,X2) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) & l3_lattices(sK0) & v17_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0))),
% 1.59/0.58    introduced(choice_axiom,[])).
% 1.59/0.58  fof(f37,plain,(
% 1.59/0.58    ? [X1] : (? [X2] : (~r3_lattices(sK0,k7_lattices(sK0,X2),k7_lattices(sK0,X1)) & r3_lattices(sK0,X1,X2) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (~r3_lattices(sK0,k7_lattices(sK0,X2),k7_lattices(sK0,sK1)) & r3_lattices(sK0,sK1,X2) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 1.59/0.58    introduced(choice_axiom,[])).
% 1.59/0.58  fof(f38,plain,(
% 1.59/0.58    ? [X2] : (~r3_lattices(sK0,k7_lattices(sK0,X2),k7_lattices(sK0,sK1)) & r3_lattices(sK0,sK1,X2) & m1_subset_1(X2,u1_struct_0(sK0))) => (~r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) & r3_lattices(sK0,sK1,sK2) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 1.59/0.58    introduced(choice_axiom,[])).
% 1.59/0.58  % (31826)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 1.59/0.58  fof(f16,plain,(
% 1.59/0.58    ? [X0] : (? [X1] : (? [X2] : (~r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) & r3_lattices(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 1.59/0.58    inference(flattening,[],[f15])).
% 1.59/0.58  fof(f15,plain,(
% 1.59/0.58    ? [X0] : (? [X1] : (? [X2] : ((~r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) & r3_lattices(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 1.59/0.58    inference(ennf_transformation,[],[f12])).
% 1.59/0.58  fof(f12,negated_conjecture,(
% 1.59/0.58    ~! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_lattices(X0,X1,X2) => r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))))))),
% 1.59/0.58    inference(negated_conjecture,[],[f11])).
% 1.59/0.58  fof(f11,conjecture,(
% 1.59/0.58    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_lattices(X0,X1,X2) => r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))))))),
% 1.59/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_lattices)).
% 1.59/0.58  fof(f219,plain,(
% 1.59/0.58    k7_lattices(sK0,sK1) != k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) | ~l3_lattices(sK0)),
% 1.59/0.58    inference(subsumption_resolution,[],[f218,f43])).
% 1.59/0.58  fof(f43,plain,(
% 1.59/0.58    ~v2_struct_0(sK0)),
% 1.59/0.58    inference(cnf_transformation,[],[f39])).
% 1.59/0.58  fof(f218,plain,(
% 1.59/0.58    k7_lattices(sK0,sK1) != k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) | v2_struct_0(sK0) | ~l3_lattices(sK0)),
% 1.59/0.58    inference(subsumption_resolution,[],[f217,f44])).
% 1.59/0.58  fof(f44,plain,(
% 1.59/0.58    v10_lattices(sK0)),
% 1.59/0.58    inference(cnf_transformation,[],[f39])).
% 1.59/0.58  fof(f217,plain,(
% 1.59/0.58    k7_lattices(sK0,sK1) != k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) | ~v10_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0)),
% 1.59/0.58    inference(resolution,[],[f216,f54])).
% 1.59/0.58  fof(f54,plain,(
% 1.59/0.58    ( ! [X0] : (v4_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f19])).
% 1.59/0.58  fof(f19,plain,(
% 1.59/0.58    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 1.59/0.58    inference(flattening,[],[f18])).
% 1.59/0.58  fof(f18,plain,(
% 1.59/0.58    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 1.59/0.58    inference(ennf_transformation,[],[f14])).
% 1.59/0.58  fof(f14,plain,(
% 1.59/0.58    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.59/0.58    inference(pure_predicate_removal,[],[f13])).
% 1.59/0.58  fof(f13,plain,(
% 1.59/0.58    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.59/0.58    inference(pure_predicate_removal,[],[f1])).
% 1.59/0.58  fof(f1,axiom,(
% 1.59/0.58    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.59/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).
% 1.59/0.58  fof(f216,plain,(
% 1.59/0.58    ~v4_lattices(sK0) | k7_lattices(sK0,sK1) != k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2))),
% 1.59/0.58    inference(subsumption_resolution,[],[f215,f46])).
% 1.59/0.58  fof(f215,plain,(
% 1.59/0.58    k7_lattices(sK0,sK1) != k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) | ~v4_lattices(sK0) | ~l3_lattices(sK0)),
% 1.59/0.58    inference(resolution,[],[f214,f52])).
% 1.59/0.58  fof(f52,plain,(
% 1.59/0.58    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f17])).
% 1.59/0.58  fof(f17,plain,(
% 1.59/0.58    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 1.59/0.58    inference(ennf_transformation,[],[f5])).
% 1.59/0.58  fof(f5,axiom,(
% 1.59/0.58    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 1.59/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).
% 1.59/0.58  fof(f214,plain,(
% 1.59/0.58    ~l2_lattices(sK0) | k7_lattices(sK0,sK1) != k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) | ~v4_lattices(sK0)),
% 1.59/0.58    inference(subsumption_resolution,[],[f213,f43])).
% 1.59/0.58  fof(f213,plain,(
% 1.59/0.58    k7_lattices(sK0,sK1) != k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) | ~l2_lattices(sK0) | ~v4_lattices(sK0) | v2_struct_0(sK0)),
% 1.59/0.58    inference(subsumption_resolution,[],[f212,f46])).
% 1.59/0.58  fof(f212,plain,(
% 1.59/0.58    k7_lattices(sK0,sK1) != k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) | ~l2_lattices(sK0) | ~v4_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0)),
% 1.59/0.58    inference(subsumption_resolution,[],[f211,f47])).
% 1.59/0.58  fof(f47,plain,(
% 1.59/0.58    m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.59/0.58    inference(cnf_transformation,[],[f39])).
% 1.59/0.58  fof(f211,plain,(
% 1.59/0.58    k7_lattices(sK0,sK1) != k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) | ~l2_lattices(sK0) | ~v4_lattices(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0)),
% 1.59/0.58    inference(resolution,[],[f210,f63])).
% 1.59/0.58  fof(f63,plain,(
% 1.59/0.58    ( ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f27])).
% 1.59/0.58  fof(f27,plain,(
% 1.59/0.58    ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.59/0.58    inference(flattening,[],[f26])).
% 1.59/0.58  fof(f26,plain,(
% 1.59/0.58    ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.59/0.58    inference(ennf_transformation,[],[f4])).
% 1.59/0.58  fof(f4,axiom,(
% 1.59/0.58    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)))),
% 1.59/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_lattices)).
% 1.59/0.58  fof(f210,plain,(
% 1.59/0.58    ~m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) | k7_lattices(sK0,sK1) != k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) | ~l2_lattices(sK0) | ~v4_lattices(sK0)),
% 1.59/0.58    inference(subsumption_resolution,[],[f209,f43])).
% 1.59/0.58  fof(f209,plain,(
% 1.59/0.58    k7_lattices(sK0,sK1) != k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) | ~m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) | ~l2_lattices(sK0) | ~v4_lattices(sK0) | v2_struct_0(sK0)),
% 1.59/0.58    inference(subsumption_resolution,[],[f208,f46])).
% 1.59/0.58  fof(f208,plain,(
% 1.59/0.58    k7_lattices(sK0,sK1) != k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) | ~m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) | ~l2_lattices(sK0) | ~v4_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0)),
% 1.59/0.58    inference(subsumption_resolution,[],[f207,f48])).
% 1.59/0.58  fof(f48,plain,(
% 1.59/0.58    m1_subset_1(sK2,u1_struct_0(sK0))),
% 1.59/0.58    inference(cnf_transformation,[],[f39])).
% 1.59/0.58  fof(f207,plain,(
% 1.59/0.58    k7_lattices(sK0,sK1) != k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) | ~m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) | ~l2_lattices(sK0) | ~v4_lattices(sK0) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0)),
% 1.59/0.58    inference(resolution,[],[f206,f63])).
% 1.59/0.58  fof(f206,plain,(
% 1.59/0.58    ~m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) | k7_lattices(sK0,sK1) != k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) | ~m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) | ~l2_lattices(sK0) | ~v4_lattices(sK0)),
% 1.59/0.58    inference(subsumption_resolution,[],[f204,f43])).
% 1.59/0.58  fof(f204,plain,(
% 1.59/0.58    k7_lattices(sK0,sK1) != k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) | ~m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) | ~m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) | ~l2_lattices(sK0) | ~v4_lattices(sK0) | v2_struct_0(sK0)),
% 1.59/0.58    inference(superposition,[],[f203,f68])).
% 1.59/0.58  fof(f68,plain,(
% 1.59/0.58    ( ! [X2,X0,X1] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f35])).
% 1.59/0.58  fof(f35,plain,(
% 1.59/0.58    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 1.59/0.58    inference(flattening,[],[f34])).
% 1.59/0.58  fof(f34,plain,(
% 1.59/0.58    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 1.59/0.58    inference(ennf_transformation,[],[f2])).
% 1.59/0.58  fof(f2,axiom,(
% 1.59/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1))),
% 1.59/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_lattices)).
% 1.59/0.58  fof(f203,plain,(
% 1.59/0.58    k7_lattices(sK0,sK1) != k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))),
% 1.59/0.58    inference(subsumption_resolution,[],[f202,f43])).
% 1.59/0.58  fof(f202,plain,(
% 1.59/0.58    k7_lattices(sK0,sK1) != k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) | v2_struct_0(sK0)),
% 1.59/0.58    inference(subsumption_resolution,[],[f201,f46])).
% 1.59/0.58  fof(f201,plain,(
% 1.59/0.58    k7_lattices(sK0,sK1) != k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) | ~l3_lattices(sK0) | v2_struct_0(sK0)),
% 1.59/0.58    inference(subsumption_resolution,[],[f200,f47])).
% 1.59/0.58  fof(f200,plain,(
% 1.59/0.58    k7_lattices(sK0,sK1) != k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0)),
% 1.59/0.58    inference(resolution,[],[f199,f63])).
% 1.59/0.58  fof(f199,plain,(
% 1.59/0.58    ~m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) | k7_lattices(sK0,sK1) != k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))),
% 1.59/0.58    inference(subsumption_resolution,[],[f198,f43])).
% 1.59/0.58  fof(f198,plain,(
% 1.59/0.58    ~m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) | k7_lattices(sK0,sK1) != k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) | v2_struct_0(sK0)),
% 1.59/0.58    inference(subsumption_resolution,[],[f197,f46])).
% 1.59/0.58  fof(f197,plain,(
% 1.59/0.58    ~m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) | k7_lattices(sK0,sK1) != k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) | ~l3_lattices(sK0) | v2_struct_0(sK0)),
% 1.59/0.58    inference(subsumption_resolution,[],[f196,f48])).
% 1.59/0.58  fof(f196,plain,(
% 1.59/0.58    ~m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) | k7_lattices(sK0,sK1) != k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0)),
% 1.59/0.58    inference(resolution,[],[f195,f63])).
% 1.59/0.58  fof(f195,plain,(
% 1.59/0.58    ~m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) | ~m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) | k7_lattices(sK0,sK1) != k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))),
% 1.59/0.58    inference(duplicate_literal_removal,[],[f194])).
% 1.59/0.58  fof(f194,plain,(
% 1.59/0.58    ~m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) | ~m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) | ~m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) | ~m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) | k7_lattices(sK0,sK1) != k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))),
% 1.59/0.58    inference(resolution,[],[f191,f79])).
% 1.59/0.58  fof(f79,plain,(
% 1.59/0.58    ( ! [X0,X1] : (r1_lattices(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k3_lattices(sK0,X0,X1) != X1) )),
% 1.59/0.58    inference(subsumption_resolution,[],[f78,f46])).
% 1.59/0.58  fof(f78,plain,(
% 1.59/0.58    ( ! [X0,X1] : (r1_lattices(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k3_lattices(sK0,X0,X1) != X1 | ~l3_lattices(sK0)) )),
% 1.59/0.58    inference(resolution,[],[f77,f52])).
% 1.59/0.58  fof(f77,plain,(
% 1.59/0.58    ( ! [X0,X1] : (~l2_lattices(sK0) | r1_lattices(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k3_lattices(sK0,X0,X1) != X1) )),
% 1.59/0.58    inference(subsumption_resolution,[],[f76,f43])).
% 1.59/0.58  fof(f76,plain,(
% 1.59/0.58    ( ! [X0,X1] : (k3_lattices(sK0,X0,X1) != X1 | r1_lattices(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l2_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.59/0.58    inference(duplicate_literal_removal,[],[f75])).
% 1.59/0.58  fof(f75,plain,(
% 1.59/0.58    ( ! [X0,X1] : (k3_lattices(sK0,X0,X1) != X1 | r1_lattices(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l2_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 1.59/0.58    inference(superposition,[],[f62,f74])).
% 1.59/0.58  fof(f74,plain,(
% 1.59/0.58    ( ! [X0,X1] : (k3_lattices(sK0,X0,X1) = k1_lattices(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 1.59/0.58    inference(subsumption_resolution,[],[f73,f46])).
% 1.59/0.58  fof(f73,plain,(
% 1.59/0.58    ( ! [X0,X1] : (k3_lattices(sK0,X0,X1) = k1_lattices(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 1.59/0.58    inference(subsumption_resolution,[],[f72,f43])).
% 1.59/0.58  fof(f72,plain,(
% 1.59/0.58    ( ! [X0,X1] : (k3_lattices(sK0,X0,X1) = k1_lattices(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 1.59/0.58    inference(resolution,[],[f71,f44])).
% 1.59/0.58  fof(f71,plain,(
% 1.59/0.58    ( ! [X2,X0,X1] : (~v10_lattices(X1) | k3_lattices(X1,X0,X2) = k1_lattices(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X1)) | v2_struct_0(X1) | ~l3_lattices(X1) | ~m1_subset_1(X0,u1_struct_0(X1))) )),
% 1.59/0.58    inference(duplicate_literal_removal,[],[f70])).
% 1.59/0.58  fof(f70,plain,(
% 1.59/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | k3_lattices(X1,X0,X2) = k1_lattices(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X1)) | v2_struct_0(X1) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X1)) )),
% 1.59/0.58    inference(resolution,[],[f69,f54])).
% 1.59/0.58  fof(f69,plain,(
% 1.59/0.58    ( ! [X2,X0,X1] : (~v4_lattices(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | k3_lattices(X1,X2,X0) = k1_lattices(X1,X2,X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | v2_struct_0(X1) | ~l3_lattices(X1)) )),
% 1.59/0.58    inference(resolution,[],[f67,f52])).
% 1.59/0.58  fof(f67,plain,(
% 1.59/0.58    ( ! [X2,X0,X1] : (~l2_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f33])).
% 1.59/0.58  fof(f33,plain,(
% 1.59/0.58    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 1.59/0.58    inference(flattening,[],[f32])).
% 1.59/0.58  fof(f32,plain,(
% 1.59/0.58    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 1.59/0.58    inference(ennf_transformation,[],[f6])).
% 1.59/0.58  fof(f6,axiom,(
% 1.59/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2))),
% 1.59/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_lattices)).
% 1.59/0.58  fof(f62,plain,(
% 1.59/0.58    ( ! [X2,X0,X1] : (k1_lattices(X0,X1,X2) != X2 | r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f41])).
% 1.59/0.58  fof(f41,plain,(
% 1.59/0.58    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k1_lattices(X0,X1,X2) != X2) & (k1_lattices(X0,X1,X2) = X2 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 1.59/0.58    inference(nnf_transformation,[],[f25])).
% 1.59/0.58  fof(f25,plain,(
% 1.59/0.58    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 1.59/0.58    inference(flattening,[],[f24])).
% 1.59/0.58  fof(f24,plain,(
% 1.59/0.58    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 1.59/0.58    inference(ennf_transformation,[],[f3])).
% 1.59/0.58  fof(f3,axiom,(
% 1.59/0.58    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2))))),
% 1.59/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_lattices)).
% 1.59/0.58  fof(f191,plain,(
% 1.59/0.58    ~r1_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) | ~m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) | ~m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))),
% 1.59/0.58    inference(resolution,[],[f190,f50])).
% 1.59/0.58  fof(f50,plain,(
% 1.59/0.58    ~r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))),
% 1.59/0.58    inference(cnf_transformation,[],[f39])).
% 1.59/0.58  fof(f190,plain,(
% 1.59/0.58    ( ! [X0,X1] : (r3_lattices(sK0,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_lattices(sK0,X1,X0)) )),
% 1.59/0.58    inference(subsumption_resolution,[],[f189,f43])).
% 1.59/0.58  fof(f189,plain,(
% 1.59/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r3_lattices(sK0,X1,X0) | v2_struct_0(sK0) | ~r1_lattices(sK0,X1,X0)) )),
% 1.59/0.58    inference(subsumption_resolution,[],[f188,f46])).
% 1.59/0.58  fof(f188,plain,(
% 1.59/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | r3_lattices(sK0,X1,X0) | v2_struct_0(sK0) | ~r1_lattices(sK0,X1,X0)) )),
% 1.59/0.58    inference(resolution,[],[f187,f44])).
% 1.59/0.58  fof(f187,plain,(
% 1.59/0.58    ( ! [X2,X0,X1] : (~v10_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r3_lattices(X0,X1,X2) | v2_struct_0(X0) | ~r1_lattices(X0,X1,X2)) )),
% 1.59/0.58    inference(subsumption_resolution,[],[f186,f55])).
% 1.59/0.58  fof(f55,plain,(
% 1.59/0.58    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f19])).
% 1.59/0.58  fof(f186,plain,(
% 1.59/0.58    ( ! [X2,X0,X1] : (~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r3_lattices(X0,X1,X2) | ~v6_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0)) )),
% 1.59/0.58    inference(subsumption_resolution,[],[f185,f56])).
% 1.59/0.58  fof(f56,plain,(
% 1.59/0.58    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f19])).
% 1.59/0.58  fof(f185,plain,(
% 1.59/0.58    ( ! [X2,X0,X1] : (~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r3_lattices(X0,X1,X2) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0)) )),
% 1.59/0.58    inference(duplicate_literal_removal,[],[f184])).
% 1.59/0.58  fof(f184,plain,(
% 1.59/0.58    ( ! [X2,X0,X1] : (~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r3_lattices(X0,X1,X2) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.59/0.58    inference(resolution,[],[f66,f57])).
% 1.59/0.58  fof(f57,plain,(
% 1.59/0.58    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f19])).
% 1.59/0.58  fof(f66,plain,(
% 1.59/0.58    ( ! [X2,X0,X1] : (~v9_lattices(X0) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r3_lattices(X0,X1,X2) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f42])).
% 1.59/0.58  fof(f42,plain,(
% 1.59/0.58    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 1.59/0.58    inference(nnf_transformation,[],[f31])).
% 1.59/0.58  fof(f31,plain,(
% 1.59/0.58    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 1.59/0.58    inference(flattening,[],[f30])).
% 1.59/0.58  fof(f30,plain,(
% 1.59/0.58    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 1.59/0.58    inference(ennf_transformation,[],[f8])).
% 1.59/0.58  fof(f8,axiom,(
% 1.59/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 1.59/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_lattices)).
% 1.59/0.58  fof(f258,plain,(
% 1.59/0.58    k7_lattices(sK0,sK1) = k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2))),
% 1.59/0.58    inference(forward_demodulation,[],[f255,f181])).
% 1.59/0.58  fof(f181,plain,(
% 1.59/0.58    sK1 = k4_lattices(sK0,sK1,sK2)),
% 1.59/0.58    inference(subsumption_resolution,[],[f180,f46])).
% 1.59/0.58  fof(f180,plain,(
% 1.59/0.58    sK1 = k4_lattices(sK0,sK1,sK2) | ~l3_lattices(sK0)),
% 1.59/0.58    inference(subsumption_resolution,[],[f179,f43])).
% 1.59/0.58  fof(f179,plain,(
% 1.59/0.58    sK1 = k4_lattices(sK0,sK1,sK2) | v2_struct_0(sK0) | ~l3_lattices(sK0)),
% 1.59/0.58    inference(subsumption_resolution,[],[f178,f44])).
% 1.59/0.58  fof(f178,plain,(
% 1.59/0.58    sK1 = k4_lattices(sK0,sK1,sK2) | ~v10_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0)),
% 1.59/0.58    inference(resolution,[],[f177,f55])).
% 1.59/0.58  fof(f177,plain,(
% 1.59/0.58    ~v6_lattices(sK0) | sK1 = k4_lattices(sK0,sK1,sK2)),
% 1.59/0.58    inference(subsumption_resolution,[],[f176,f46])).
% 1.59/0.58  fof(f176,plain,(
% 1.59/0.58    sK1 = k4_lattices(sK0,sK1,sK2) | ~v6_lattices(sK0) | ~l3_lattices(sK0)),
% 1.59/0.58    inference(resolution,[],[f155,f51])).
% 1.59/0.58  fof(f51,plain,(
% 1.59/0.58    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f17])).
% 1.59/0.58  fof(f155,plain,(
% 1.59/0.58    ~l1_lattices(sK0) | sK1 = k4_lattices(sK0,sK1,sK2) | ~v6_lattices(sK0)),
% 1.59/0.58    inference(subsumption_resolution,[],[f154,f43])).
% 1.59/0.58  fof(f154,plain,(
% 1.59/0.58    sK1 = k4_lattices(sK0,sK1,sK2) | ~l1_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0)),
% 1.59/0.58    inference(subsumption_resolution,[],[f153,f47])).
% 1.59/0.58  fof(f153,plain,(
% 1.59/0.58    sK1 = k4_lattices(sK0,sK1,sK2) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0)),
% 1.59/0.58    inference(subsumption_resolution,[],[f149,f48])).
% 1.59/0.58  fof(f149,plain,(
% 1.59/0.58    sK1 = k4_lattices(sK0,sK1,sK2) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0)),
% 1.59/0.58    inference(superposition,[],[f145,f64])).
% 1.59/0.58  fof(f64,plain,(
% 1.59/0.58    ( ! [X2,X0,X1] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f29])).
% 1.59/0.58  fof(f29,plain,(
% 1.59/0.58    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 1.59/0.58    inference(flattening,[],[f28])).
% 1.59/0.58  fof(f28,plain,(
% 1.59/0.58    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 1.59/0.58    inference(ennf_transformation,[],[f7])).
% 1.59/0.58  fof(f7,axiom,(
% 1.59/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2))),
% 1.59/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_lattices)).
% 1.59/0.58  % (31810)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 1.59/0.58  fof(f145,plain,(
% 1.59/0.58    sK1 = k2_lattices(sK0,sK1,sK2)),
% 1.59/0.58    inference(subsumption_resolution,[],[f144,f48])).
% 1.59/0.58  fof(f144,plain,(
% 1.59/0.58    sK1 = k2_lattices(sK0,sK1,sK2) | ~m1_subset_1(sK2,u1_struct_0(sK0))),
% 1.59/0.58    inference(subsumption_resolution,[],[f142,f47])).
% 1.59/0.58  fof(f142,plain,(
% 1.59/0.58    ~m1_subset_1(sK1,u1_struct_0(sK0)) | sK1 = k2_lattices(sK0,sK1,sK2) | ~m1_subset_1(sK2,u1_struct_0(sK0))),
% 1.59/0.58    inference(resolution,[],[f141,f105])).
% 1.59/0.58  fof(f105,plain,(
% 1.59/0.58    ( ! [X0,X1] : (~r1_lattices(sK0,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k2_lattices(sK0,X1,X0) = X1 | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 1.59/0.58    inference(subsumption_resolution,[],[f104,f43])).
% 1.59/0.58  fof(f104,plain,(
% 1.59/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k2_lattices(sK0,X1,X0) = X1 | v2_struct_0(sK0) | ~r1_lattices(sK0,X1,X0)) )),
% 1.59/0.58    inference(subsumption_resolution,[],[f103,f46])).
% 1.59/0.58  fof(f103,plain,(
% 1.59/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | k2_lattices(sK0,X1,X0) = X1 | v2_struct_0(sK0) | ~r1_lattices(sK0,X1,X0)) )),
% 1.59/0.58    inference(resolution,[],[f102,f44])).
% 1.59/0.58  fof(f102,plain,(
% 1.59/0.58    ( ! [X2,X0,X1] : (~v10_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | k2_lattices(X0,X1,X2) = X1 | v2_struct_0(X0) | ~r1_lattices(X0,X1,X2)) )),
% 1.59/0.58    inference(subsumption_resolution,[],[f101,f56])).
% 1.59/0.58  fof(f101,plain,(
% 1.59/0.58    ( ! [X2,X0,X1] : (~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | k2_lattices(X0,X1,X2) = X1 | ~v8_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0)) )),
% 1.59/0.58    inference(duplicate_literal_removal,[],[f100])).
% 1.59/0.58  fof(f100,plain,(
% 1.59/0.58    ( ! [X2,X0,X1] : (~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | k2_lattices(X0,X1,X2) = X1 | ~v8_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.59/0.58    inference(resolution,[],[f59,f57])).
% 1.59/0.58  fof(f59,plain,(
% 1.59/0.58    ( ! [X2,X0,X1] : (~v9_lattices(X0) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | k2_lattices(X0,X1,X2) = X1 | ~v8_lattices(X0) | v2_struct_0(X0)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f40])).
% 1.59/0.58  fof(f40,plain,(
% 1.59/0.58    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) != X1) & (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 1.59/0.58    inference(nnf_transformation,[],[f23])).
% 1.59/0.58  fof(f23,plain,(
% 1.59/0.58    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 1.59/0.58    inference(flattening,[],[f22])).
% 1.59/0.58  fof(f22,plain,(
% 1.59/0.58    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)))),
% 1.59/0.58    inference(ennf_transformation,[],[f9])).
% 1.59/0.58  fof(f9,axiom,(
% 1.59/0.58    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1))))),
% 1.59/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_lattices)).
% 1.59/0.58  fof(f141,plain,(
% 1.59/0.58    r1_lattices(sK0,sK1,sK2)),
% 1.59/0.58    inference(subsumption_resolution,[],[f140,f48])).
% 1.59/0.58  fof(f140,plain,(
% 1.59/0.58    r1_lattices(sK0,sK1,sK2) | ~m1_subset_1(sK2,u1_struct_0(sK0))),
% 1.59/0.58    inference(subsumption_resolution,[],[f139,f47])).
% 1.59/0.58  fof(f139,plain,(
% 1.59/0.58    ~m1_subset_1(sK1,u1_struct_0(sK0)) | r1_lattices(sK0,sK1,sK2) | ~m1_subset_1(sK2,u1_struct_0(sK0))),
% 1.59/0.58    inference(resolution,[],[f138,f49])).
% 1.59/0.58  fof(f49,plain,(
% 1.59/0.58    r3_lattices(sK0,sK1,sK2)),
% 1.59/0.58    inference(cnf_transformation,[],[f39])).
% 1.59/0.58  fof(f138,plain,(
% 1.59/0.58    ( ! [X0,X1] : (~r3_lattices(sK0,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_lattices(sK0,X1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 1.59/0.58    inference(subsumption_resolution,[],[f137,f43])).
% 1.59/0.58  fof(f137,plain,(
% 1.59/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_lattices(sK0,X1,X0) | v2_struct_0(sK0) | ~r3_lattices(sK0,X1,X0)) )),
% 1.59/0.58    inference(subsumption_resolution,[],[f136,f46])).
% 1.59/0.58  fof(f136,plain,(
% 1.59/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | r1_lattices(sK0,X1,X0) | v2_struct_0(sK0) | ~r3_lattices(sK0,X1,X0)) )),
% 1.59/0.58    inference(resolution,[],[f135,f44])).
% 1.59/0.58  fof(f135,plain,(
% 1.59/0.58    ( ! [X2,X0,X1] : (~v10_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r1_lattices(X0,X1,X2) | v2_struct_0(X0) | ~r3_lattices(X0,X1,X2)) )),
% 1.59/0.58    inference(subsumption_resolution,[],[f134,f55])).
% 1.59/0.58  fof(f134,plain,(
% 1.59/0.58    ( ! [X2,X0,X1] : (~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r1_lattices(X0,X1,X2) | ~v6_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0)) )),
% 1.59/0.58    inference(subsumption_resolution,[],[f133,f56])).
% 1.59/0.58  fof(f133,plain,(
% 1.59/0.58    ( ! [X2,X0,X1] : (~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r1_lattices(X0,X1,X2) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0)) )),
% 1.59/0.58    inference(duplicate_literal_removal,[],[f132])).
% 1.59/0.58  fof(f132,plain,(
% 1.59/0.58    ( ! [X2,X0,X1] : (~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r1_lattices(X0,X1,X2) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.59/0.58    inference(resolution,[],[f65,f57])).
% 1.59/0.58  fof(f65,plain,(
% 1.59/0.58    ( ! [X2,X0,X1] : (~v9_lattices(X0) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r1_lattices(X0,X1,X2) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f42])).
% 1.59/0.58  fof(f255,plain,(
% 1.59/0.58    k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) = k7_lattices(sK0,k4_lattices(sK0,sK1,sK2))),
% 1.59/0.58    inference(resolution,[],[f226,f47])).
% 1.59/0.58  fof(f226,plain,(
% 1.59/0.58    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | k7_lattices(sK0,k4_lattices(sK0,X1,sK2)) = k3_lattices(sK0,k7_lattices(sK0,X1),k7_lattices(sK0,sK2))) )),
% 1.59/0.58    inference(resolution,[],[f224,f48])).
% 1.59/0.58  fof(f224,plain,(
% 1.59/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k7_lattices(sK0,k4_lattices(sK0,X1,X0)) = k3_lattices(sK0,k7_lattices(sK0,X1),k7_lattices(sK0,X0))) )),
% 1.59/0.58    inference(subsumption_resolution,[],[f223,f43])).
% 1.59/0.58  fof(f223,plain,(
% 1.59/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k7_lattices(sK0,k4_lattices(sK0,X1,X0)) = k3_lattices(sK0,k7_lattices(sK0,X1),k7_lattices(sK0,X0)) | v2_struct_0(sK0)) )),
% 1.59/0.58    inference(subsumption_resolution,[],[f222,f44])).
% 1.59/0.58  fof(f222,plain,(
% 1.59/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k7_lattices(sK0,k4_lattices(sK0,X1,X0)) = k3_lattices(sK0,k7_lattices(sK0,X1),k7_lattices(sK0,X0)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.59/0.58    inference(subsumption_resolution,[],[f221,f46])).
% 1.59/0.58  fof(f221,plain,(
% 1.59/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | k7_lattices(sK0,k4_lattices(sK0,X1,X0)) = k3_lattices(sK0,k7_lattices(sK0,X1),k7_lattices(sK0,X0)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.59/0.58    inference(resolution,[],[f58,f45])).
% 1.59/0.58  fof(f45,plain,(
% 1.59/0.58    v17_lattices(sK0)),
% 1.59/0.58    inference(cnf_transformation,[],[f39])).
% 1.59/0.58  fof(f58,plain,(
% 1.59/0.58    ( ! [X2,X0,X1] : (~v17_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | k7_lattices(X0,k4_lattices(X0,X1,X2)) = k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.59/0.58    inference(cnf_transformation,[],[f21])).
% 1.59/0.58  fof(f21,plain,(
% 1.59/0.58    ! [X0] : (! [X1] : (! [X2] : (k7_lattices(X0,k4_lattices(X0,X1,X2)) = k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.59/0.58    inference(flattening,[],[f20])).
% 1.59/0.58  fof(f20,plain,(
% 1.59/0.58    ! [X0] : (! [X1] : (! [X2] : (k7_lattices(X0,k4_lattices(X0,X1,X2)) = k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 1.59/0.58    inference(ennf_transformation,[],[f10])).
% 1.59/0.58  fof(f10,axiom,(
% 1.59/0.58    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k7_lattices(X0,k4_lattices(X0,X1,X2)) = k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)))))),
% 1.59/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_lattices)).
% 1.59/0.58  % SZS output end Proof for theBenchmark
% 1.59/0.58  % (31825)------------------------------
% 1.59/0.58  % (31825)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.58  % (31825)Termination reason: Refutation
% 1.59/0.58  
% 1.59/0.58  % (31825)Memory used [KB]: 6268
% 1.59/0.58  % (31825)Time elapsed: 0.143 s
% 1.59/0.58  % (31825)------------------------------
% 1.59/0.58  % (31825)------------------------------
% 1.59/0.59  % (31805)Success in time 0.216 s
%------------------------------------------------------------------------------
