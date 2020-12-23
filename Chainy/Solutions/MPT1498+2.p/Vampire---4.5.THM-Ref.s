%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1498+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:22 EST 2020

% Result     : Theorem 1.43s
% Output     : Refutation 1.43s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 941 expanded)
%              Number of leaves         :    7 ( 264 expanded)
%              Depth                    :   20
%              Number of atoms          :  214 (6613 expanded)
%              Number of equality atoms :   10 (  60 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3331,plain,(
    $false ),
    inference(global_subsumption,[],[f3144,f3267,f3330])).

fof(f3330,plain,(
    ~ r2_lattice3(k3_lattice3(sK1),sK0,sK2) ),
    inference(forward_demodulation,[],[f3326,f3152])).

fof(f3152,plain,(
    sK2 = k4_lattice3(sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f3032,f3033,f3034,f3143,f3087])).

fof(f3087,plain,(
    ! [X0,X1] :
      ( k4_lattice3(X0,X1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2960])).

fof(f2960,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattice3(X0,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2959])).

fof(f2959,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattice3(X0,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2822])).

fof(f2822,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k4_lattice3(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_lattice3)).

fof(f3143,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f3141,f3140])).

fof(f3140,plain,(
    sK2 = k5_lattice3(sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f3032,f3033,f3034,f3035,f3043])).

fof(f3043,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
      | k5_lattice3(X0,X1) = X1
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2928])).

fof(f2928,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_lattice3(X0,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0))) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2927])).

fof(f2927,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_lattice3(X0,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0))) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2823])).

fof(f2823,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
         => k5_lattice3(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_lattice3)).

fof(f3035,plain,(
    m1_subset_1(sK2,u1_struct_0(k3_lattice3(sK1))) ),
    inference(cnf_transformation,[],[f2975])).

fof(f2975,plain,
    ( ( ~ r4_lattice3(sK1,k5_lattice3(sK1,sK2),sK0)
      | ~ r2_lattice3(k3_lattice3(sK1),sK0,sK2) )
    & ( r4_lattice3(sK1,k5_lattice3(sK1,sK2),sK0)
      | r2_lattice3(k3_lattice3(sK1),sK0,sK2) )
    & m1_subset_1(sK2,u1_struct_0(k3_lattice3(sK1)))
    & l3_lattices(sK1)
    & v10_lattices(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f2972,f2974,f2973])).

fof(f2973,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r4_lattice3(X1,k5_lattice3(X1,X2),X0)
              | ~ r2_lattice3(k3_lattice3(X1),X0,X2) )
            & ( r4_lattice3(X1,k5_lattice3(X1,X2),X0)
              | r2_lattice3(k3_lattice3(X1),X0,X2) )
            & m1_subset_1(X2,u1_struct_0(k3_lattice3(X1))) )
        & l3_lattices(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ( ~ r4_lattice3(sK1,k5_lattice3(sK1,X2),sK0)
            | ~ r2_lattice3(k3_lattice3(sK1),sK0,X2) )
          & ( r4_lattice3(sK1,k5_lattice3(sK1,X2),sK0)
            | r2_lattice3(k3_lattice3(sK1),sK0,X2) )
          & m1_subset_1(X2,u1_struct_0(k3_lattice3(sK1))) )
      & l3_lattices(sK1)
      & v10_lattices(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f2974,plain,
    ( ? [X2] :
        ( ( ~ r4_lattice3(sK1,k5_lattice3(sK1,X2),sK0)
          | ~ r2_lattice3(k3_lattice3(sK1),sK0,X2) )
        & ( r4_lattice3(sK1,k5_lattice3(sK1,X2),sK0)
          | r2_lattice3(k3_lattice3(sK1),sK0,X2) )
        & m1_subset_1(X2,u1_struct_0(k3_lattice3(sK1))) )
   => ( ( ~ r4_lattice3(sK1,k5_lattice3(sK1,sK2),sK0)
        | ~ r2_lattice3(k3_lattice3(sK1),sK0,sK2) )
      & ( r4_lattice3(sK1,k5_lattice3(sK1,sK2),sK0)
        | r2_lattice3(k3_lattice3(sK1),sK0,sK2) )
      & m1_subset_1(sK2,u1_struct_0(k3_lattice3(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f2972,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r4_lattice3(X1,k5_lattice3(X1,X2),X0)
            | ~ r2_lattice3(k3_lattice3(X1),X0,X2) )
          & ( r4_lattice3(X1,k5_lattice3(X1,X2),X0)
            | r2_lattice3(k3_lattice3(X1),X0,X2) )
          & m1_subset_1(X2,u1_struct_0(k3_lattice3(X1))) )
      & l3_lattices(X1)
      & v10_lattices(X1)
      & ~ v2_struct_0(X1) ) ),
    inference(flattening,[],[f2971])).

fof(f2971,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r4_lattice3(X1,k5_lattice3(X1,X2),X0)
            | ~ r2_lattice3(k3_lattice3(X1),X0,X2) )
          & ( r4_lattice3(X1,k5_lattice3(X1,X2),X0)
            | r2_lattice3(k3_lattice3(X1),X0,X2) )
          & m1_subset_1(X2,u1_struct_0(k3_lattice3(X1))) )
      & l3_lattices(X1)
      & v10_lattices(X1)
      & ~ v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f2922])).

fof(f2922,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r2_lattice3(k3_lattice3(X1),X0,X2)
          <~> r4_lattice3(X1,k5_lattice3(X1,X2),X0) )
          & m1_subset_1(X2,u1_struct_0(k3_lattice3(X1))) )
      & l3_lattices(X1)
      & v10_lattices(X1)
      & ~ v2_struct_0(X1) ) ),
    inference(flattening,[],[f2921])).

fof(f2921,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r2_lattice3(k3_lattice3(X1),X0,X2)
          <~> r4_lattice3(X1,k5_lattice3(X1,X2),X0) )
          & m1_subset_1(X2,u1_struct_0(k3_lattice3(X1))) )
      & l3_lattices(X1)
      & v10_lattices(X1)
      & ~ v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f2900])).

fof(f2900,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( l3_lattices(X1)
          & v10_lattices(X1)
          & ~ v2_struct_0(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(k3_lattice3(X1)))
           => ( r2_lattice3(k3_lattice3(X1),X0,X2)
            <=> r4_lattice3(X1,k5_lattice3(X1,X2),X0) ) ) ) ),
    inference(negated_conjecture,[],[f2899])).

fof(f2899,conjecture,(
    ! [X0,X1] :
      ( ( l3_lattices(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(k3_lattice3(X1)))
         => ( r2_lattice3(k3_lattice3(X1),X0,X2)
          <=> r4_lattice3(X1,k5_lattice3(X1,X2),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_lattice3)).

fof(f3141,plain,(
    m1_subset_1(k5_lattice3(sK1,sK2),u1_struct_0(sK1)) ),
    inference(unit_resulting_resolution,[],[f3032,f3033,f3034,f3035,f3042])).

fof(f3042,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_lattice3(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2926])).

fof(f2926,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_lattice3(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2925])).

fof(f2925,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_lattice3(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2839])).

fof(f2839,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
        & l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattice3)).

fof(f3034,plain,(
    l3_lattices(sK1) ),
    inference(cnf_transformation,[],[f2975])).

fof(f3033,plain,(
    v10_lattices(sK1) ),
    inference(cnf_transformation,[],[f2975])).

fof(f3032,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f2975])).

fof(f3326,plain,(
    ~ r2_lattice3(k3_lattice3(sK1),sK0,k4_lattice3(sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f3032,f3033,f3034,f3143,f3267,f3045])).

fof(f3045,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2))
      | r4_lattice3(X1,X2,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f2980])).

fof(f2980,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r4_lattice3(X1,X2,X0)
              | ~ r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2)) )
            & ( r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2))
              | ~ r4_lattice3(X1,X2,X0) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X1)) )
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f2930])).

fof(f2930,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r4_lattice3(X1,X2,X0)
          <=> r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2)) )
          | ~ m1_subset_1(X2,u1_struct_0(X1)) )
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f2929])).

fof(f2929,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r4_lattice3(X1,X2,X0)
          <=> r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2)) )
          | ~ m1_subset_1(X2,u1_struct_0(X1)) )
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f2898])).

fof(f2898,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( r4_lattice3(X1,X2,X0)
          <=> r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_lattice3)).

fof(f3267,plain,(
    ~ r4_lattice3(sK1,sK2,sK0) ),
    inference(duplicate_literal_removal,[],[f3266])).

fof(f3266,plain,
    ( ~ r4_lattice3(sK1,sK2,sK0)
    | ~ r4_lattice3(sK1,sK2,sK0) ),
    inference(resolution,[],[f3165,f3145])).

fof(f3145,plain,
    ( ~ r2_lattice3(k3_lattice3(sK1),sK0,sK2)
    | ~ r4_lattice3(sK1,sK2,sK0) ),
    inference(backward_demodulation,[],[f3037,f3140])).

fof(f3037,plain,
    ( ~ r4_lattice3(sK1,k5_lattice3(sK1,sK2),sK0)
    | ~ r2_lattice3(k3_lattice3(sK1),sK0,sK2) ),
    inference(cnf_transformation,[],[f2975])).

fof(f3165,plain,(
    ! [X0] :
      ( r2_lattice3(k3_lattice3(sK1),X0,sK2)
      | ~ r4_lattice3(sK1,sK2,X0) ) ),
    inference(subsumption_resolution,[],[f3164,f3032])).

fof(f3164,plain,(
    ! [X0] :
      ( r2_lattice3(k3_lattice3(sK1),X0,sK2)
      | ~ r4_lattice3(sK1,sK2,X0)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f3163,f3033])).

fof(f3163,plain,(
    ! [X0] :
      ( r2_lattice3(k3_lattice3(sK1),X0,sK2)
      | ~ r4_lattice3(sK1,sK2,X0)
      | ~ v10_lattices(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f3162,f3034])).

fof(f3162,plain,(
    ! [X0] :
      ( r2_lattice3(k3_lattice3(sK1),X0,sK2)
      | ~ r4_lattice3(sK1,sK2,X0)
      | ~ l3_lattices(sK1)
      | ~ v10_lattices(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f3155,f3143])).

% (8610)dis+11_2_add=large:afr=on:anc=none:gs=on:gsem=on:lwlo=on:nm=16:nwc=1:sd=1:ss=axioms:st=3.0:sos=on_4 on theBenchmark
fof(f3155,plain,(
    ! [X0] :
      ( r2_lattice3(k3_lattice3(sK1),X0,sK2)
      | ~ r4_lattice3(sK1,sK2,X0)
      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
      | ~ l3_lattices(sK1)
      | ~ v10_lattices(sK1)
      | v2_struct_0(sK1) ) ),
    inference(superposition,[],[f3044,f3152])).

fof(f3044,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2))
      | ~ r4_lattice3(X1,X2,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f2980])).

fof(f3144,plain,
    ( r2_lattice3(k3_lattice3(sK1),sK0,sK2)
    | r4_lattice3(sK1,sK2,sK0) ),
    inference(backward_demodulation,[],[f3036,f3140])).

fof(f3036,plain,
    ( r4_lattice3(sK1,k5_lattice3(sK1,sK2),sK0)
    | r2_lattice3(k3_lattice3(sK1),sK0,sK2) ),
    inference(cnf_transformation,[],[f2975])).
%------------------------------------------------------------------------------
