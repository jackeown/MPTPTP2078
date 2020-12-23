%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1212+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:12 EST 2020

% Result     : Theorem 2.52s
% Output     : Refutation 2.52s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 320 expanded)
%              Number of leaves         :   11 (  99 expanded)
%              Depth                    :   22
%              Number of atoms          :  407 (1791 expanded)
%              Number of equality atoms :   60 ( 312 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6000,plain,(
    $false ),
    inference(subsumption_resolution,[],[f5999,f3297])).

fof(f3297,plain,(
    k6_lattices(sK22) != k3_lattices(sK22,k7_lattices(sK22,sK23),sK23) ),
    inference(cnf_transformation,[],[f2822])).

fof(f2822,plain,
    ( k6_lattices(sK22) != k3_lattices(sK22,k7_lattices(sK22,sK23),sK23)
    & m1_subset_1(sK23,u1_struct_0(sK22))
    & l3_lattices(sK22)
    & v17_lattices(sK22)
    & v10_lattices(sK22)
    & ~ v2_struct_0(sK22) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK22,sK23])],[f2100,f2821,f2820])).

fof(f2820,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k6_lattices(X0) != k3_lattices(X0,k7_lattices(X0,X1),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k6_lattices(sK22) != k3_lattices(sK22,k7_lattices(sK22,X1),X1)
          & m1_subset_1(X1,u1_struct_0(sK22)) )
      & l3_lattices(sK22)
      & v17_lattices(sK22)
      & v10_lattices(sK22)
      & ~ v2_struct_0(sK22) ) ),
    introduced(choice_axiom,[])).

fof(f2821,plain,
    ( ? [X1] :
        ( k6_lattices(sK22) != k3_lattices(sK22,k7_lattices(sK22,X1),X1)
        & m1_subset_1(X1,u1_struct_0(sK22)) )
   => ( k6_lattices(sK22) != k3_lattices(sK22,k7_lattices(sK22,sK23),sK23)
      & m1_subset_1(sK23,u1_struct_0(sK22)) ) ),
    introduced(choice_axiom,[])).

fof(f2100,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k6_lattices(X0) != k3_lattices(X0,k7_lattices(X0,X1),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f2099])).

fof(f2099,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k6_lattices(X0) != k3_lattices(X0,k7_lattices(X0,X1),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2073])).

fof(f2073,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v17_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => k6_lattices(X0) = k3_lattices(X0,k7_lattices(X0,X1),X1) ) ) ),
    inference(negated_conjecture,[],[f2072])).

fof(f2072,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k6_lattices(X0) = k3_lattices(X0,k7_lattices(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_lattices)).

fof(f5999,plain,(
    k6_lattices(sK22) = k3_lattices(sK22,k7_lattices(sK22,sK23),sK23) ),
    inference(forward_demodulation,[],[f5987,f5943])).

fof(f5943,plain,(
    k6_lattices(sK22) = k1_lattices(sK22,k7_lattices(sK22,sK23),sK23) ),
    inference(subsumption_resolution,[],[f5942,f3292])).

fof(f3292,plain,(
    ~ v2_struct_0(sK22) ),
    inference(cnf_transformation,[],[f2822])).

fof(f5942,plain,
    ( k6_lattices(sK22) = k1_lattices(sK22,k7_lattices(sK22,sK23),sK23)
    | v2_struct_0(sK22) ),
    inference(subsumption_resolution,[],[f5941,f3295])).

fof(f3295,plain,(
    l3_lattices(sK22) ),
    inference(cnf_transformation,[],[f2822])).

fof(f5941,plain,
    ( k6_lattices(sK22) = k1_lattices(sK22,k7_lattices(sK22,sK23),sK23)
    | ~ l3_lattices(sK22)
    | v2_struct_0(sK22) ),
    inference(subsumption_resolution,[],[f5940,f4524])).

fof(f4524,plain,(
    m1_subset_1(k7_lattices(sK22,sK23),u1_struct_0(sK22)) ),
    inference(subsumption_resolution,[],[f4523,f3292])).

fof(f4523,plain,
    ( m1_subset_1(k7_lattices(sK22,sK23),u1_struct_0(sK22))
    | v2_struct_0(sK22) ),
    inference(subsumption_resolution,[],[f4473,f3295])).

fof(f4473,plain,
    ( m1_subset_1(k7_lattices(sK22,sK23),u1_struct_0(sK22))
    | ~ l3_lattices(sK22)
    | v2_struct_0(sK22) ),
    inference(resolution,[],[f3296,f3356])).

fof(f3356,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2143])).

fof(f2143,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2142])).

fof(f2142,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2038])).

fof(f2038,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_lattices)).

fof(f3296,plain,(
    m1_subset_1(sK23,u1_struct_0(sK22)) ),
    inference(cnf_transformation,[],[f2822])).

fof(f5940,plain,
    ( k6_lattices(sK22) = k1_lattices(sK22,k7_lattices(sK22,sK23),sK23)
    | ~ m1_subset_1(k7_lattices(sK22,sK23),u1_struct_0(sK22))
    | ~ l3_lattices(sK22)
    | v2_struct_0(sK22) ),
    inference(subsumption_resolution,[],[f5935,f3296])).

fof(f5935,plain,
    ( k6_lattices(sK22) = k1_lattices(sK22,k7_lattices(sK22,sK23),sK23)
    | ~ m1_subset_1(sK23,u1_struct_0(sK22))
    | ~ m1_subset_1(k7_lattices(sK22,sK23),u1_struct_0(sK22))
    | ~ l3_lattices(sK22)
    | v2_struct_0(sK22) ),
    inference(resolution,[],[f4663,f3362])).

fof(f3362,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_lattices(X0,X1,X2)
      | k6_lattices(X0) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2866])).

fof(f2866,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_lattices(X0,X1,X2)
                  | k5_lattices(X0) != k2_lattices(X0,X2,X1)
                  | k2_lattices(X0,X1,X2) != k5_lattices(X0)
                  | k6_lattices(X0) != k1_lattices(X0,X2,X1)
                  | k6_lattices(X0) != k1_lattices(X0,X1,X2) )
                & ( ( k5_lattices(X0) = k2_lattices(X0,X2,X1)
                    & k2_lattices(X0,X1,X2) = k5_lattices(X0)
                    & k6_lattices(X0) = k1_lattices(X0,X2,X1)
                    & k6_lattices(X0) = k1_lattices(X0,X1,X2) )
                  | ~ r2_lattices(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2865])).

fof(f2865,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_lattices(X0,X1,X2)
                  | k5_lattices(X0) != k2_lattices(X0,X2,X1)
                  | k2_lattices(X0,X1,X2) != k5_lattices(X0)
                  | k6_lattices(X0) != k1_lattices(X0,X2,X1)
                  | k6_lattices(X0) != k1_lattices(X0,X1,X2) )
                & ( ( k5_lattices(X0) = k2_lattices(X0,X2,X1)
                    & k2_lattices(X0,X1,X2) = k5_lattices(X0)
                    & k6_lattices(X0) = k1_lattices(X0,X2,X1)
                    & k6_lattices(X0) = k1_lattices(X0,X1,X2) )
                  | ~ r2_lattices(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f2153])).

fof(f2153,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_lattices(X0,X1,X2)
              <=> ( k5_lattices(X0) = k2_lattices(X0,X2,X1)
                  & k2_lattices(X0,X1,X2) = k5_lattices(X0)
                  & k6_lattices(X0) = k1_lattices(X0,X2,X1)
                  & k6_lattices(X0) = k1_lattices(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2152])).

fof(f2152,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_lattices(X0,X1,X2)
              <=> ( k5_lattices(X0) = k2_lattices(X0,X2,X1)
                  & k2_lattices(X0,X1,X2) = k5_lattices(X0)
                  & k6_lattices(X0) = k1_lattices(X0,X2,X1)
                  & k6_lattices(X0) = k1_lattices(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2021])).

fof(f2021,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_lattices(X0,X1,X2)
              <=> ( k5_lattices(X0) = k2_lattices(X0,X2,X1)
                  & k2_lattices(X0,X1,X2) = k5_lattices(X0)
                  & k6_lattices(X0) = k1_lattices(X0,X2,X1)
                  & k6_lattices(X0) = k1_lattices(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_lattices)).

fof(f4663,plain,(
    r2_lattices(sK22,k7_lattices(sK22,sK23),sK23) ),
    inference(subsumption_resolution,[],[f4662,f3296])).

fof(f4662,plain,
    ( r2_lattices(sK22,k7_lattices(sK22,sK23),sK23)
    | ~ m1_subset_1(sK23,u1_struct_0(sK22)) ),
    inference(subsumption_resolution,[],[f4661,f3292])).

fof(f4661,plain,
    ( r2_lattices(sK22,k7_lattices(sK22,sK23),sK23)
    | v2_struct_0(sK22)
    | ~ m1_subset_1(sK23,u1_struct_0(sK22)) ),
    inference(subsumption_resolution,[],[f4660,f3293])).

fof(f3293,plain,(
    v10_lattices(sK22) ),
    inference(cnf_transformation,[],[f2822])).

fof(f4660,plain,
    ( r2_lattices(sK22,k7_lattices(sK22,sK23),sK23)
    | ~ v10_lattices(sK22)
    | v2_struct_0(sK22)
    | ~ m1_subset_1(sK23,u1_struct_0(sK22)) ),
    inference(subsumption_resolution,[],[f4659,f4439])).

fof(f4439,plain,(
    v11_lattices(sK22) ),
    inference(subsumption_resolution,[],[f4438,f3295])).

fof(f4438,plain,
    ( v11_lattices(sK22)
    | ~ l3_lattices(sK22) ),
    inference(subsumption_resolution,[],[f4435,f3292])).

fof(f4435,plain,
    ( v11_lattices(sK22)
    | v2_struct_0(sK22)
    | ~ l3_lattices(sK22) ),
    inference(resolution,[],[f3294,f3441])).

fof(f3441,plain,(
    ! [X0] :
      ( ~ v17_lattices(X0)
      | v11_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f2210])).

fof(f2210,plain,(
    ! [X0] :
      ( ( v16_lattices(X0)
        & v15_lattices(X0)
        & v11_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f2209])).

fof(f2209,plain,(
    ! [X0] :
      ( ( v16_lattices(X0)
        & v15_lattices(X0)
        & v11_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f2013])).

fof(f2013,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v17_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v16_lattices(X0)
          & v15_lattices(X0)
          & v11_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_lattices)).

fof(f3294,plain,(
    v17_lattices(sK22) ),
    inference(cnf_transformation,[],[f2822])).

fof(f4659,plain,
    ( r2_lattices(sK22,k7_lattices(sK22,sK23),sK23)
    | ~ v11_lattices(sK22)
    | ~ v10_lattices(sK22)
    | v2_struct_0(sK22)
    | ~ m1_subset_1(sK23,u1_struct_0(sK22)) ),
    inference(subsumption_resolution,[],[f4658,f4443])).

fof(f4443,plain,(
    v16_lattices(sK22) ),
    inference(subsumption_resolution,[],[f4442,f3295])).

fof(f4442,plain,
    ( v16_lattices(sK22)
    | ~ l3_lattices(sK22) ),
    inference(subsumption_resolution,[],[f4437,f3292])).

fof(f4437,plain,
    ( v16_lattices(sK22)
    | v2_struct_0(sK22)
    | ~ l3_lattices(sK22) ),
    inference(resolution,[],[f3294,f3443])).

fof(f3443,plain,(
    ! [X0] :
      ( ~ v17_lattices(X0)
      | v16_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f2210])).

fof(f4658,plain,
    ( r2_lattices(sK22,k7_lattices(sK22,sK23),sK23)
    | ~ v16_lattices(sK22)
    | ~ v11_lattices(sK22)
    | ~ v10_lattices(sK22)
    | v2_struct_0(sK22)
    | ~ m1_subset_1(sK23,u1_struct_0(sK22)) ),
    inference(subsumption_resolution,[],[f4622,f3295])).

fof(f4622,plain,
    ( r2_lattices(sK22,k7_lattices(sK22,sK23),sK23)
    | ~ l3_lattices(sK22)
    | ~ v16_lattices(sK22)
    | ~ v11_lattices(sK22)
    | ~ v10_lattices(sK22)
    | v2_struct_0(sK22)
    | ~ m1_subset_1(sK23,u1_struct_0(sK22)) ),
    inference(resolution,[],[f4524,f4417])).

fof(f4417,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | r2_lattices(X0,k7_lattices(X0,X1),X1)
      | ~ l3_lattices(X0)
      | ~ v16_lattices(X0)
      | ~ v11_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f4327])).

fof(f4327,plain,(
    ! [X0,X1] :
      ( r2_lattices(X0,k7_lattices(X0,X1),X1)
      | ~ m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v16_lattices(X0)
      | ~ v11_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f3358])).

fof(f3358,plain,(
    ! [X2,X0,X1] :
      ( r2_lattices(X0,X2,X1)
      | k7_lattices(X0,X1) != X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v16_lattices(X0)
      | ~ v11_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2864])).

fof(f2864,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k7_lattices(X0,X1) = X2
                  | ~ r2_lattices(X0,X2,X1) )
                & ( r2_lattices(X0,X2,X1)
                  | k7_lattices(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l3_lattices(X0)
          | ~ v16_lattices(X0)
          | ~ v11_lattices(X0)
          | ~ v10_lattices(X0)
          | v2_struct_0(X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f2147])).

fof(f2147,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k7_lattices(X0,X1) = X2
              <=> r2_lattices(X0,X2,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l3_lattices(X0)
          | ~ v16_lattices(X0)
          | ~ v11_lattices(X0)
          | ~ v10_lattices(X0)
          | v2_struct_0(X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2146])).

fof(f2146,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k7_lattices(X0,X1) = X2
              <=> r2_lattices(X0,X2,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l3_lattices(X0)
          | ~ v16_lattices(X0)
          | ~ v11_lattices(X0)
          | ~ v10_lattices(X0)
          | v2_struct_0(X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2023])).

fof(f2023,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( ( l3_lattices(X0)
              & v16_lattices(X0)
              & v11_lattices(X0)
              & v10_lattices(X0)
              & ~ v2_struct_0(X0) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( k7_lattices(X0,X1) = X2
                <=> r2_lattices(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d21_lattices)).

fof(f5987,plain,(
    k3_lattices(sK22,k7_lattices(sK22,sK23),sK23) = k1_lattices(sK22,k7_lattices(sK22,sK23),sK23) ),
    inference(resolution,[],[f4504,f4524])).

fof(f4504,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK22))
      | k3_lattices(sK22,X1,sK23) = k1_lattices(sK22,X1,sK23) ) ),
    inference(subsumption_resolution,[],[f4503,f3292])).

fof(f4503,plain,(
    ! [X1] :
      ( k3_lattices(sK22,X1,sK23) = k1_lattices(sK22,X1,sK23)
      | ~ m1_subset_1(X1,u1_struct_0(sK22))
      | v2_struct_0(sK22) ) ),
    inference(subsumption_resolution,[],[f4502,f4458])).

fof(f4458,plain,(
    v4_lattices(sK22) ),
    inference(resolution,[],[f4426,f3447])).

fof(f3447,plain,(
    ! [X0] :
      ( ~ sP2(X0)
      | v4_lattices(X0) ) ),
    inference(cnf_transformation,[],[f2902])).

fof(f2902,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ sP2(X0) ) ),
    inference(nnf_transformation,[],[f2785])).

fof(f2785,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ sP2(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f4426,plain,(
    sP2(sK22) ),
    inference(subsumption_resolution,[],[f4425,f3295])).

fof(f4425,plain,
    ( sP2(sK22)
    | ~ l3_lattices(sK22) ),
    inference(subsumption_resolution,[],[f4420,f3292])).

fof(f4420,plain,
    ( sP2(sK22)
    | v2_struct_0(sK22)
    | ~ l3_lattices(sK22) ),
    inference(resolution,[],[f3293,f3453])).

fof(f3453,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | sP2(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f2786])).

fof(f2786,plain,(
    ! [X0] :
      ( sP2(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(definition_folding,[],[f2216,f2785])).

fof(f2216,plain,(
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
    inference(flattening,[],[f2215])).

fof(f2215,plain,(
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
    inference(ennf_transformation,[],[f2009])).

fof(f2009,axiom,(
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

fof(f4502,plain,(
    ! [X1] :
      ( k3_lattices(sK22,X1,sK23) = k1_lattices(sK22,X1,sK23)
      | ~ m1_subset_1(X1,u1_struct_0(sK22))
      | ~ v4_lattices(sK22)
      | v2_struct_0(sK22) ) ),
    inference(subsumption_resolution,[],[f4465,f4452])).

fof(f4452,plain,(
    l2_lattices(sK22) ),
    inference(resolution,[],[f3295,f3437])).

fof(f3437,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | l2_lattices(X0) ) ),
    inference(cnf_transformation,[],[f2206])).

fof(f2206,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f2041])).

fof(f2041,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f4465,plain,(
    ! [X1] :
      ( k3_lattices(sK22,X1,sK23) = k1_lattices(sK22,X1,sK23)
      | ~ m1_subset_1(X1,u1_struct_0(sK22))
      | ~ l2_lattices(sK22)
      | ~ v4_lattices(sK22)
      | v2_struct_0(sK22) ) ),
    inference(resolution,[],[f3296,f3334])).

fof(f3334,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2125])).

fof(f2125,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2124])).

fof(f2124,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2047])).

fof(f2047,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_lattices)).
%------------------------------------------------------------------------------
