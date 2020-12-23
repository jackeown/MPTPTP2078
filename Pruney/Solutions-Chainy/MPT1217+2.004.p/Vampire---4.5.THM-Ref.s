%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:45 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 655 expanded)
%              Number of leaves         :   11 ( 247 expanded)
%              Depth                    :   16
%              Number of atoms          :  433 (4680 expanded)
%              Number of equality atoms :   66 (  88 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f458,plain,(
    $false ),
    inference(subsumption_resolution,[],[f457,f211])).

fof(f211,plain,(
    k5_lattices(sK0) != k4_lattices(sK0,k7_lattices(sK0,sK2),sK1) ),
    inference(subsumption_resolution,[],[f210,f30])).

fof(f30,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ~ r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))
    & r3_lattices(sK0,sK1,sK2)
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v17_lattices(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f27,f26,f25])).

fof(f25,plain,
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

fof(f26,plain,
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

fof(f27,plain,
    ( ? [X2] :
        ( ~ r3_lattices(sK0,k7_lattices(sK0,X2),k7_lattices(sK0,sK1))
        & r3_lattices(sK0,sK1,X2)
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ~ r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))
      & r3_lattices(sK0,sK1,sK2)
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
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
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
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

fof(f210,plain,
    ( k5_lattices(sK0) != k4_lattices(sK0,k7_lattices(sK0,sK2),sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f209,f31])).

fof(f31,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f209,plain,
    ( k5_lattices(sK0) != k4_lattices(sK0,k7_lattices(sK0,sK2),sK1)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f208,f32])).

fof(f32,plain,(
    v17_lattices(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f208,plain,
    ( k5_lattices(sK0) != k4_lattices(sK0,k7_lattices(sK0,sK2),sK1)
    | ~ v17_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f207,f33])).

fof(f33,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f207,plain,
    ( k5_lattices(sK0) != k4_lattices(sK0,k7_lattices(sK0,sK2),sK1)
    | ~ l3_lattices(sK0)
    | ~ v17_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f206,f201])).

fof(f201,plain,(
    m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f200,f30])).

fof(f200,plain,
    ( m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f169,f33])).

fof(f169,plain,
    ( m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f35,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
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

fof(f35,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f206,plain,
    ( k5_lattices(sK0) != k4_lattices(sK0,k7_lattices(sK0,sK2),sK1)
    | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v17_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f205,f34])).

fof(f34,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f205,plain,
    ( k5_lattices(sK0) != k4_lattices(sK0,k7_lattices(sK0,sK2),sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v17_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f37,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,X1,k7_lattices(X0,X2))
      | k4_lattices(X0,X1,X2) != k5_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k4_lattices(X0,X1,X2) = k5_lattices(X0)
                  | ~ r3_lattices(X0,X1,k7_lattices(X0,X2)) )
                & ( r3_lattices(X0,X1,k7_lattices(X0,X2))
                  | k4_lattices(X0,X1,X2) != k5_lattices(X0) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_lattices)).

fof(f37,plain,(
    ~ r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f457,plain,(
    k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,sK2),sK1) ),
    inference(backward_demodulation,[],[f444,f456])).

fof(f456,plain,(
    k5_lattices(sK0) = k7_lattices(sK0,k3_lattices(sK0,sK2,k7_lattices(sK0,sK1))) ),
    inference(forward_demodulation,[],[f455,f364])).

fof(f364,plain,(
    k5_lattices(sK0) = k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f363,f201])).

fof(f363,plain,
    ( k5_lattices(sK0) = k4_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f359,f36])).

fof(f36,plain,(
    r3_lattices(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f359,plain,
    ( ~ r3_lattices(sK0,sK1,sK2)
    | k5_lattices(sK0) = k4_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) ),
    inference(superposition,[],[f151,f175])).

fof(f175,plain,(
    sK2 = k7_lattices(sK0,k7_lattices(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f174,f30])).

fof(f174,plain,
    ( sK2 = k7_lattices(sK0,k7_lattices(sK0,sK2))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f173,f31])).

fof(f173,plain,
    ( sK2 = k7_lattices(sK0,k7_lattices(sK0,sK2))
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f172,f32])).

fof(f172,plain,
    ( sK2 = k7_lattices(sK0,k7_lattices(sK0,sK2))
    | ~ v17_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f162,f33])).

fof(f162,plain,
    ( sK2 = k7_lattices(sK0,k7_lattices(sK0,sK2))
    | ~ l3_lattices(sK0)
    | ~ v17_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f35,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k7_lattices(X0,k7_lattices(X0,X1)) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_lattices(X0,k7_lattices(X0,X1)) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_lattices)).

fof(f151,plain,(
    ! [X4] :
      ( ~ r3_lattices(sK0,sK1,k7_lattices(sK0,X4))
      | k5_lattices(sK0) = k4_lattices(sK0,sK1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f150,f30])).

fof(f150,plain,(
    ! [X4] :
      ( k5_lattices(sK0) = k4_lattices(sK0,sK1,X4)
      | ~ r3_lattices(sK0,sK1,k7_lattices(sK0,X4))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f149,f31])).

fof(f149,plain,(
    ! [X4] :
      ( k5_lattices(sK0) = k4_lattices(sK0,sK1,X4)
      | ~ r3_lattices(sK0,sK1,k7_lattices(sK0,X4))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f148,f32])).

fof(f148,plain,(
    ! [X4] :
      ( k5_lattices(sK0) = k4_lattices(sK0,sK1,X4)
      | ~ r3_lattices(sK0,sK1,k7_lattices(sK0,X4))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ v17_lattices(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f123,f33])).

fof(f123,plain,(
    ! [X4] :
      ( k5_lattices(sK0) = k4_lattices(sK0,sK1,X4)
      | ~ r3_lattices(sK0,sK1,k7_lattices(sK0,X4))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v17_lattices(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f34,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k4_lattices(X0,X1,X2) = k5_lattices(X0)
      | ~ r3_lattices(X0,X1,k7_lattices(X0,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f455,plain,(
    k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)) = k7_lattices(sK0,k3_lattices(sK0,sK2,k7_lattices(sK0,sK1))) ),
    inference(forward_demodulation,[],[f454,f346])).

fof(f346,plain,(
    k3_lattices(sK0,sK2,k7_lattices(sK0,sK1)) = k3_lattices(sK0,k7_lattices(sK0,sK1),sK2) ),
    inference(resolution,[],[f204,f157])).

fof(f157,plain,(
    m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f156,f30])).

fof(f156,plain,
    ( m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f125,f33])).

fof(f125,plain,
    ( m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f34,f51])).

fof(f204,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,u1_struct_0(sK0))
      | k3_lattices(sK0,sK2,X6) = k3_lattices(sK0,X6,sK2) ) ),
    inference(subsumption_resolution,[],[f203,f30])).

fof(f203,plain,(
    ! [X6] :
      ( k3_lattices(sK0,sK2,X6) = k3_lattices(sK0,X6,sK2)
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f202,f66])).

fof(f66,plain,(
    v4_lattices(sK0) ),
    inference(subsumption_resolution,[],[f65,f33])).

fof(f65,plain,
    ( v4_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f53,f31])).

fof(f53,plain,
    ( v4_lattices(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f30,f41])).

fof(f41,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f1])).

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

fof(f202,plain,(
    ! [X6] :
      ( k3_lattices(sK0,sK2,X6) = k3_lattices(sK0,X6,sK2)
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ v4_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f170,f106])).

fof(f106,plain,(
    l2_lattices(sK0) ),
    inference(resolution,[],[f33,f39])).

fof(f39,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f170,plain,(
    ! [X6] :
      ( k3_lattices(sK0,sK2,X6) = k3_lattices(sK0,X6,sK2)
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ l2_lattices(sK0)
      | ~ v4_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f35,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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

fof(f454,plain,(
    k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)) = k7_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK1),sK2)) ),
    inference(forward_demodulation,[],[f449,f131])).

fof(f131,plain,(
    sK1 = k7_lattices(sK0,k7_lattices(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f130,f30])).

fof(f130,plain,
    ( sK1 = k7_lattices(sK0,k7_lattices(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f129,f31])).

fof(f129,plain,
    ( sK1 = k7_lattices(sK0,k7_lattices(sK0,sK1))
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f128,f32])).

fof(f128,plain,
    ( sK1 = k7_lattices(sK0,k7_lattices(sK0,sK1))
    | ~ v17_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f118,f33])).

fof(f118,plain,
    ( sK1 = k7_lattices(sK0,k7_lattices(sK0,sK1))
    | ~ l3_lattices(sK0)
    | ~ v17_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f34,f47])).

fof(f449,plain,(
    k7_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK1),sK2)) = k4_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,sK2)) ),
    inference(resolution,[],[f183,f157])).

fof(f183,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | k7_lattices(sK0,k3_lattices(sK0,X1,sK2)) = k4_lattices(sK0,k7_lattices(sK0,X1),k7_lattices(sK0,sK2)) ) ),
    inference(subsumption_resolution,[],[f182,f30])).

fof(f182,plain,(
    ! [X1] :
      ( k7_lattices(sK0,k3_lattices(sK0,X1,sK2)) = k4_lattices(sK0,k7_lattices(sK0,X1),k7_lattices(sK0,sK2))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f181,f31])).

fof(f181,plain,(
    ! [X1] :
      ( k7_lattices(sK0,k3_lattices(sK0,X1,sK2)) = k4_lattices(sK0,k7_lattices(sK0,X1),k7_lattices(sK0,sK2))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f180,f32])).

fof(f180,plain,(
    ! [X1] :
      ( k7_lattices(sK0,k3_lattices(sK0,X1,sK2)) = k4_lattices(sK0,k7_lattices(sK0,X1),k7_lattices(sK0,sK2))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v17_lattices(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f164,f33])).

fof(f164,plain,(
    ! [X1] :
      ( k7_lattices(sK0,k3_lattices(sK0,X1,sK2)) = k4_lattices(sK0,k7_lattices(sK0,X1),k7_lattices(sK0,sK2))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v17_lattices(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f35,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
             => k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_lattices)).

fof(f444,plain,(
    k4_lattices(sK0,k7_lattices(sK0,sK2),sK1) = k7_lattices(sK0,k3_lattices(sK0,sK2,k7_lattices(sK0,sK1))) ),
    inference(forward_demodulation,[],[f439,f131])).

fof(f439,plain,(
    k7_lattices(sK0,k3_lattices(sK0,sK2,k7_lattices(sK0,sK1))) = k4_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,k7_lattices(sK0,sK1))) ),
    inference(resolution,[],[f179,f157])).

fof(f179,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k7_lattices(sK0,k3_lattices(sK0,sK2,X0)) = k4_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f178,f30])).

fof(f178,plain,(
    ! [X0] :
      ( k7_lattices(sK0,k3_lattices(sK0,sK2,X0)) = k4_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f177,f31])).

fof(f177,plain,(
    ! [X0] :
      ( k7_lattices(sK0,k3_lattices(sK0,sK2,X0)) = k4_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f176,f32])).

fof(f176,plain,(
    ! [X0] :
      ( k7_lattices(sK0,k3_lattices(sK0,sK2,X0)) = k4_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v17_lattices(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f163,f33])).

fof(f163,plain,(
    ! [X0] :
      ( k7_lattices(sK0,k3_lattices(sK0,sK2,X0)) = k4_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v17_lattices(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f35,f48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:41:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (30720)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.51  % (30728)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.51  % (30711)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.52  % (30720)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (30718)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.53  % (30723)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f458,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(subsumption_resolution,[],[f457,f211])).
% 0.21/0.53  fof(f211,plain,(
% 0.21/0.53    k5_lattices(sK0) != k4_lattices(sK0,k7_lattices(sK0,sK2),sK1)),
% 0.21/0.53    inference(subsumption_resolution,[],[f210,f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ~v2_struct_0(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ((~r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) & r3_lattices(sK0,sK1,sK2) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l3_lattices(sK0) & v17_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f27,f26,f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (~r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) & r3_lattices(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (~r3_lattices(sK0,k7_lattices(sK0,X2),k7_lattices(sK0,X1)) & r3_lattices(sK0,X1,X2) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) & l3_lattices(sK0) & v17_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ? [X1] : (? [X2] : (~r3_lattices(sK0,k7_lattices(sK0,X2),k7_lattices(sK0,X1)) & r3_lattices(sK0,X1,X2) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (~r3_lattices(sK0,k7_lattices(sK0,X2),k7_lattices(sK0,sK1)) & r3_lattices(sK0,sK1,X2) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ? [X2] : (~r3_lattices(sK0,k7_lattices(sK0,X2),k7_lattices(sK0,sK1)) & r3_lattices(sK0,sK1,X2) & m1_subset_1(X2,u1_struct_0(sK0))) => (~r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) & r3_lattices(sK0,sK1,sK2) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f11,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (~r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) & r3_lattices(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f10])).
% 0.21/0.53  fof(f10,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : ((~r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) & r3_lattices(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,negated_conjecture,(
% 0.21/0.53    ~! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_lattices(X0,X1,X2) => r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))))))),
% 0.21/0.53    inference(negated_conjecture,[],[f8])).
% 0.21/0.53  fof(f8,conjecture,(
% 0.21/0.53    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_lattices(X0,X1,X2) => r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_lattices)).
% 0.21/0.53  fof(f210,plain,(
% 0.21/0.53    k5_lattices(sK0) != k4_lattices(sK0,k7_lattices(sK0,sK2),sK1) | v2_struct_0(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f209,f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    v10_lattices(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f28])).
% 0.21/0.53  fof(f209,plain,(
% 0.21/0.53    k5_lattices(sK0) != k4_lattices(sK0,k7_lattices(sK0,sK2),sK1) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f208,f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    v17_lattices(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f28])).
% 0.21/0.53  fof(f208,plain,(
% 0.21/0.53    k5_lattices(sK0) != k4_lattices(sK0,k7_lattices(sK0,sK2),sK1) | ~v17_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f207,f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    l3_lattices(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f28])).
% 0.21/0.53  fof(f207,plain,(
% 0.21/0.53    k5_lattices(sK0) != k4_lattices(sK0,k7_lattices(sK0,sK2),sK1) | ~l3_lattices(sK0) | ~v17_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f206,f201])).
% 0.21/0.53  fof(f201,plain,(
% 0.21/0.53    m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))),
% 0.21/0.53    inference(subsumption_resolution,[],[f200,f30])).
% 0.21/0.53  fof(f200,plain,(
% 0.21/0.53    m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) | v2_struct_0(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f169,f33])).
% 0.21/0.53  fof(f169,plain,(
% 0.21/0.53    m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.53    inference(resolution,[],[f35,f51])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_lattices)).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.21/0.53    inference(cnf_transformation,[],[f28])).
% 0.21/0.53  fof(f206,plain,(
% 0.21/0.53    k5_lattices(sK0) != k4_lattices(sK0,k7_lattices(sK0,sK2),sK1) | ~m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v17_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f205,f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.53    inference(cnf_transformation,[],[f28])).
% 0.21/0.53  fof(f205,plain,(
% 0.21/0.53    k5_lattices(sK0) != k4_lattices(sK0,k7_lattices(sK0,sK2),sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v17_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.53    inference(resolution,[],[f37,f49])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r3_lattices(X0,X1,k7_lattices(X0,X2)) | k4_lattices(X0,X1,X2) != k5_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (((k4_lattices(X0,X1,X2) = k5_lattices(X0) | ~r3_lattices(X0,X1,k7_lattices(X0,X2))) & (r3_lattices(X0,X1,k7_lattices(X0,X2)) | k4_lattices(X0,X1,X2) != k5_lattices(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : ((k4_lattices(X0,X1,X2) = k5_lattices(X0) <=> r3_lattices(X0,X1,k7_lattices(X0,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : ((k4_lattices(X0,X1,X2) = k5_lattices(X0) <=> r3_lattices(X0,X1,k7_lattices(X0,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k4_lattices(X0,X1,X2) = k5_lattices(X0) <=> r3_lattices(X0,X1,k7_lattices(X0,X2))))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_lattices)).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ~r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))),
% 0.21/0.53    inference(cnf_transformation,[],[f28])).
% 0.21/0.53  fof(f457,plain,(
% 0.21/0.53    k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,sK2),sK1)),
% 0.21/0.53    inference(backward_demodulation,[],[f444,f456])).
% 0.21/0.53  fof(f456,plain,(
% 0.21/0.53    k5_lattices(sK0) = k7_lattices(sK0,k3_lattices(sK0,sK2,k7_lattices(sK0,sK1)))),
% 0.21/0.53    inference(forward_demodulation,[],[f455,f364])).
% 0.21/0.53  fof(f364,plain,(
% 0.21/0.53    k5_lattices(sK0) = k4_lattices(sK0,sK1,k7_lattices(sK0,sK2))),
% 0.21/0.53    inference(subsumption_resolution,[],[f363,f201])).
% 0.21/0.53  fof(f363,plain,(
% 0.21/0.53    k5_lattices(sK0) = k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)) | ~m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))),
% 0.21/0.53    inference(subsumption_resolution,[],[f359,f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    r3_lattices(sK0,sK1,sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f28])).
% 0.21/0.53  fof(f359,plain,(
% 0.21/0.53    ~r3_lattices(sK0,sK1,sK2) | k5_lattices(sK0) = k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)) | ~m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))),
% 0.21/0.53    inference(superposition,[],[f151,f175])).
% 0.21/0.53  fof(f175,plain,(
% 0.21/0.53    sK2 = k7_lattices(sK0,k7_lattices(sK0,sK2))),
% 0.21/0.53    inference(subsumption_resolution,[],[f174,f30])).
% 0.21/0.53  fof(f174,plain,(
% 0.21/0.53    sK2 = k7_lattices(sK0,k7_lattices(sK0,sK2)) | v2_struct_0(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f173,f31])).
% 0.21/0.53  fof(f173,plain,(
% 0.21/0.53    sK2 = k7_lattices(sK0,k7_lattices(sK0,sK2)) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f172,f32])).
% 0.21/0.53  fof(f172,plain,(
% 0.21/0.53    sK2 = k7_lattices(sK0,k7_lattices(sK0,sK2)) | ~v17_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f162,f33])).
% 0.21/0.53  fof(f162,plain,(
% 0.21/0.53    sK2 = k7_lattices(sK0,k7_lattices(sK0,sK2)) | ~l3_lattices(sK0) | ~v17_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.53    inference(resolution,[],[f35,f47])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k7_lattices(X0,k7_lattices(X0,X1)) = X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (k7_lattices(X0,k7_lattices(X0,X1)) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (k7_lattices(X0,k7_lattices(X0,X1)) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k7_lattices(X0,k7_lattices(X0,X1)) = X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_lattices)).
% 0.21/0.53  fof(f151,plain,(
% 0.21/0.53    ( ! [X4] : (~r3_lattices(sK0,sK1,k7_lattices(sK0,X4)) | k5_lattices(sK0) = k4_lattices(sK0,sK1,X4) | ~m1_subset_1(X4,u1_struct_0(sK0))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f150,f30])).
% 0.21/0.53  fof(f150,plain,(
% 0.21/0.53    ( ! [X4] : (k5_lattices(sK0) = k4_lattices(sK0,sK1,X4) | ~r3_lattices(sK0,sK1,k7_lattices(sK0,X4)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f149,f31])).
% 0.21/0.53  fof(f149,plain,(
% 0.21/0.53    ( ! [X4] : (k5_lattices(sK0) = k4_lattices(sK0,sK1,X4) | ~r3_lattices(sK0,sK1,k7_lattices(sK0,X4)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f148,f32])).
% 0.21/0.53  fof(f148,plain,(
% 0.21/0.53    ( ! [X4] : (k5_lattices(sK0) = k4_lattices(sK0,sK1,X4) | ~r3_lattices(sK0,sK1,k7_lattices(sK0,X4)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~v17_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f123,f33])).
% 0.21/0.53  fof(f123,plain,(
% 0.21/0.53    ( ! [X4] : (k5_lattices(sK0) = k4_lattices(sK0,sK1,X4) | ~r3_lattices(sK0,sK1,k7_lattices(sK0,X4)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v17_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.53    inference(resolution,[],[f34,f50])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k4_lattices(X0,X1,X2) = k5_lattices(X0) | ~r3_lattices(X0,X1,k7_lattices(X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f455,plain,(
% 0.21/0.53    k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)) = k7_lattices(sK0,k3_lattices(sK0,sK2,k7_lattices(sK0,sK1)))),
% 0.21/0.53    inference(forward_demodulation,[],[f454,f346])).
% 0.21/0.53  fof(f346,plain,(
% 0.21/0.53    k3_lattices(sK0,sK2,k7_lattices(sK0,sK1)) = k3_lattices(sK0,k7_lattices(sK0,sK1),sK2)),
% 0.21/0.53    inference(resolution,[],[f204,f157])).
% 0.21/0.53  fof(f157,plain,(
% 0.21/0.53    m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))),
% 0.21/0.53    inference(subsumption_resolution,[],[f156,f30])).
% 0.21/0.53  fof(f156,plain,(
% 0.21/0.53    m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) | v2_struct_0(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f125,f33])).
% 0.21/0.53  fof(f125,plain,(
% 0.21/0.53    m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.53    inference(resolution,[],[f34,f51])).
% 0.21/0.53  fof(f204,plain,(
% 0.21/0.53    ( ! [X6] : (~m1_subset_1(X6,u1_struct_0(sK0)) | k3_lattices(sK0,sK2,X6) = k3_lattices(sK0,X6,sK2)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f203,f30])).
% 0.21/0.53  fof(f203,plain,(
% 0.21/0.53    ( ! [X6] : (k3_lattices(sK0,sK2,X6) = k3_lattices(sK0,X6,sK2) | ~m1_subset_1(X6,u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f202,f66])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    v4_lattices(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f65,f33])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    v4_lattices(sK0) | ~l3_lattices(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f53,f31])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    v4_lattices(sK0) | ~v10_lattices(sK0) | ~l3_lattices(sK0)),
% 0.21/0.53    inference(resolution,[],[f30,f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ( ! [X0] : (v4_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 0.21/0.53    inference(flattening,[],[f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).
% 0.21/0.53  fof(f202,plain,(
% 0.21/0.53    ( ! [X6] : (k3_lattices(sK0,sK2,X6) = k3_lattices(sK0,X6,sK2) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~v4_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f170,f106])).
% 0.21/0.53  fof(f106,plain,(
% 0.21/0.53    l2_lattices(sK0)),
% 0.21/0.53    inference(resolution,[],[f33,f39])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,plain,(
% 0.21/0.53    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).
% 0.21/0.53  fof(f170,plain,(
% 0.21/0.53    ( ! [X6] : (k3_lattices(sK0,sK2,X6) = k3_lattices(sK0,X6,sK2) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~l2_lattices(sK0) | ~v4_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.53    inference(resolution,[],[f35,f52])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_lattices)).
% 0.21/0.53  fof(f454,plain,(
% 0.21/0.53    k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)) = k7_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK1),sK2))),
% 0.21/0.53    inference(forward_demodulation,[],[f449,f131])).
% 0.21/0.53  fof(f131,plain,(
% 0.21/0.53    sK1 = k7_lattices(sK0,k7_lattices(sK0,sK1))),
% 0.21/0.53    inference(subsumption_resolution,[],[f130,f30])).
% 0.21/0.53  fof(f130,plain,(
% 0.21/0.53    sK1 = k7_lattices(sK0,k7_lattices(sK0,sK1)) | v2_struct_0(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f129,f31])).
% 0.21/0.53  fof(f129,plain,(
% 0.21/0.53    sK1 = k7_lattices(sK0,k7_lattices(sK0,sK1)) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f128,f32])).
% 0.21/0.53  fof(f128,plain,(
% 0.21/0.53    sK1 = k7_lattices(sK0,k7_lattices(sK0,sK1)) | ~v17_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f118,f33])).
% 0.21/0.53  fof(f118,plain,(
% 0.21/0.53    sK1 = k7_lattices(sK0,k7_lattices(sK0,sK1)) | ~l3_lattices(sK0) | ~v17_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.53    inference(resolution,[],[f34,f47])).
% 0.21/0.53  fof(f449,plain,(
% 0.21/0.53    k7_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK1),sK2)) = k4_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,sK2))),
% 0.21/0.53    inference(resolution,[],[f183,f157])).
% 0.21/0.53  fof(f183,plain,(
% 0.21/0.53    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | k7_lattices(sK0,k3_lattices(sK0,X1,sK2)) = k4_lattices(sK0,k7_lattices(sK0,X1),k7_lattices(sK0,sK2))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f182,f30])).
% 0.21/0.53  fof(f182,plain,(
% 0.21/0.53    ( ! [X1] : (k7_lattices(sK0,k3_lattices(sK0,X1,sK2)) = k4_lattices(sK0,k7_lattices(sK0,X1),k7_lattices(sK0,sK2)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f181,f31])).
% 0.21/0.53  fof(f181,plain,(
% 0.21/0.53    ( ! [X1] : (k7_lattices(sK0,k3_lattices(sK0,X1,sK2)) = k4_lattices(sK0,k7_lattices(sK0,X1),k7_lattices(sK0,sK2)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f180,f32])).
% 0.21/0.53  fof(f180,plain,(
% 0.21/0.53    ( ! [X1] : (k7_lattices(sK0,k3_lattices(sK0,X1,sK2)) = k4_lattices(sK0,k7_lattices(sK0,X1),k7_lattices(sK0,sK2)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v17_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f164,f33])).
% 0.21/0.53  fof(f164,plain,(
% 0.21/0.53    ( ! [X1] : (k7_lattices(sK0,k3_lattices(sK0,X1,sK2)) = k4_lattices(sK0,k7_lattices(sK0,X1),k7_lattices(sK0,sK2)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v17_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.53    inference(resolution,[],[f35,f48])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v17_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0] : ((l3_lattices(X0) & v17_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k7_lattices(X0,k3_lattices(X0,X1,X2)) = k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_lattices)).
% 0.21/0.53  fof(f444,plain,(
% 0.21/0.53    k4_lattices(sK0,k7_lattices(sK0,sK2),sK1) = k7_lattices(sK0,k3_lattices(sK0,sK2,k7_lattices(sK0,sK1)))),
% 0.21/0.53    inference(forward_demodulation,[],[f439,f131])).
% 0.21/0.53  fof(f439,plain,(
% 0.21/0.53    k7_lattices(sK0,k3_lattices(sK0,sK2,k7_lattices(sK0,sK1))) = k4_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,k7_lattices(sK0,sK1)))),
% 0.21/0.53    inference(resolution,[],[f179,f157])).
% 0.21/0.53  fof(f179,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k7_lattices(sK0,k3_lattices(sK0,sK2,X0)) = k4_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,X0))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f178,f30])).
% 0.21/0.53  fof(f178,plain,(
% 0.21/0.53    ( ! [X0] : (k7_lattices(sK0,k3_lattices(sK0,sK2,X0)) = k4_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f177,f31])).
% 0.21/0.53  fof(f177,plain,(
% 0.21/0.53    ( ! [X0] : (k7_lattices(sK0,k3_lattices(sK0,sK2,X0)) = k4_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f176,f32])).
% 0.21/0.53  fof(f176,plain,(
% 0.21/0.53    ( ! [X0] : (k7_lattices(sK0,k3_lattices(sK0,sK2,X0)) = k4_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v17_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f163,f33])).
% 0.21/0.53  fof(f163,plain,(
% 0.21/0.53    ( ! [X0] : (k7_lattices(sK0,k3_lattices(sK0,sK2,X0)) = k4_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v17_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.53    inference(resolution,[],[f35,f48])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (30720)------------------------------
% 0.21/0.53  % (30720)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (30720)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (30720)Memory used [KB]: 1791
% 0.21/0.53  % (30720)Time elapsed: 0.080 s
% 0.21/0.53  % (30720)------------------------------
% 0.21/0.53  % (30720)------------------------------
% 0.21/0.53  % (30715)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.54  % (30703)Success in time 0.174 s
%------------------------------------------------------------------------------
