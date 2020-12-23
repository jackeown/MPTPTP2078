%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1211+2 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 0.67s
% Output     : Refutation 0.67s
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
fof(f5932,plain,(
    $false ),
    inference(subsumption_resolution,[],[f5931,f3294])).

fof(f3294,plain,(
    k5_lattices(sK22) != k4_lattices(sK22,k7_lattices(sK22,sK23),sK23) ),
    inference(cnf_transformation,[],[f2819])).

fof(f2819,plain,
    ( k5_lattices(sK22) != k4_lattices(sK22,k7_lattices(sK22,sK23),sK23)
    & m1_subset_1(sK23,u1_struct_0(sK22))
    & l3_lattices(sK22)
    & v17_lattices(sK22)
    & v10_lattices(sK22)
    & ~ v2_struct_0(sK22) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK22,sK23])],[f2099,f2818,f2817])).

fof(f2817,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k5_lattices(X0) != k4_lattices(X0,k7_lattices(X0,X1),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k5_lattices(sK22) != k4_lattices(sK22,k7_lattices(sK22,X1),X1)
          & m1_subset_1(X1,u1_struct_0(sK22)) )
      & l3_lattices(sK22)
      & v17_lattices(sK22)
      & v10_lattices(sK22)
      & ~ v2_struct_0(sK22) ) ),
    introduced(choice_axiom,[])).

fof(f2818,plain,
    ( ? [X1] :
        ( k5_lattices(sK22) != k4_lattices(sK22,k7_lattices(sK22,X1),X1)
        & m1_subset_1(X1,u1_struct_0(sK22)) )
   => ( k5_lattices(sK22) != k4_lattices(sK22,k7_lattices(sK22,sK23),sK23)
      & m1_subset_1(sK23,u1_struct_0(sK22)) ) ),
    introduced(choice_axiom,[])).

fof(f2099,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k5_lattices(X0) != k4_lattices(X0,k7_lattices(X0,X1),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f2098])).

fof(f2098,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k5_lattices(X0) != k4_lattices(X0,k7_lattices(X0,X1),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2072])).

fof(f2072,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v17_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => k5_lattices(X0) = k4_lattices(X0,k7_lattices(X0,X1),X1) ) ) ),
    inference(negated_conjecture,[],[f2071])).

fof(f2071,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k5_lattices(X0) = k4_lattices(X0,k7_lattices(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_lattices)).

fof(f5931,plain,(
    k5_lattices(sK22) = k4_lattices(sK22,k7_lattices(sK22,sK23),sK23) ),
    inference(forward_demodulation,[],[f5920,f5909])).

fof(f5909,plain,(
    k5_lattices(sK22) = k2_lattices(sK22,k7_lattices(sK22,sK23),sK23) ),
    inference(subsumption_resolution,[],[f5908,f3289])).

fof(f3289,plain,(
    ~ v2_struct_0(sK22) ),
    inference(cnf_transformation,[],[f2819])).

fof(f5908,plain,
    ( k5_lattices(sK22) = k2_lattices(sK22,k7_lattices(sK22,sK23),sK23)
    | v2_struct_0(sK22) ),
    inference(subsumption_resolution,[],[f5907,f3292])).

fof(f3292,plain,(
    l3_lattices(sK22) ),
    inference(cnf_transformation,[],[f2819])).

fof(f5907,plain,
    ( k5_lattices(sK22) = k2_lattices(sK22,k7_lattices(sK22,sK23),sK23)
    | ~ l3_lattices(sK22)
    | v2_struct_0(sK22) ),
    inference(subsumption_resolution,[],[f5906,f4528])).

fof(f4528,plain,(
    m1_subset_1(k7_lattices(sK22,sK23),u1_struct_0(sK22)) ),
    inference(subsumption_resolution,[],[f4527,f3289])).

fof(f4527,plain,
    ( m1_subset_1(k7_lattices(sK22,sK23),u1_struct_0(sK22))
    | v2_struct_0(sK22) ),
    inference(subsumption_resolution,[],[f4471,f3292])).

fof(f4471,plain,
    ( m1_subset_1(k7_lattices(sK22,sK23),u1_struct_0(sK22))
    | ~ l3_lattices(sK22)
    | v2_struct_0(sK22) ),
    inference(resolution,[],[f3293,f3355])).

fof(f3355,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2146])).

fof(f2146,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2145])).

fof(f2145,plain,(
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

fof(f3293,plain,(
    m1_subset_1(sK23,u1_struct_0(sK22)) ),
    inference(cnf_transformation,[],[f2819])).

fof(f5906,plain,
    ( k5_lattices(sK22) = k2_lattices(sK22,k7_lattices(sK22,sK23),sK23)
    | ~ m1_subset_1(k7_lattices(sK22,sK23),u1_struct_0(sK22))
    | ~ l3_lattices(sK22)
    | v2_struct_0(sK22) ),
    inference(subsumption_resolution,[],[f5894,f3293])).

fof(f5894,plain,
    ( k5_lattices(sK22) = k2_lattices(sK22,k7_lattices(sK22,sK23),sK23)
    | ~ m1_subset_1(sK23,u1_struct_0(sK22))
    | ~ m1_subset_1(k7_lattices(sK22,sK23),u1_struct_0(sK22))
    | ~ l3_lattices(sK22)
    | v2_struct_0(sK22) ),
    inference(resolution,[],[f4662,f3362])).

fof(f3362,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_lattices(X0,X1,X2)
      | k2_lattices(X0,X1,X2) = k5_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2863])).

fof(f2863,plain,(
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
    inference(flattening,[],[f2862])).

fof(f2862,plain,(
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
    inference(nnf_transformation,[],[f2154])).

fof(f2154,plain,(
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
    inference(flattening,[],[f2153])).

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

fof(f4662,plain,(
    r2_lattices(sK22,k7_lattices(sK22,sK23),sK23) ),
    inference(subsumption_resolution,[],[f4661,f3293])).

fof(f4661,plain,
    ( r2_lattices(sK22,k7_lattices(sK22,sK23),sK23)
    | ~ m1_subset_1(sK23,u1_struct_0(sK22)) ),
    inference(subsumption_resolution,[],[f4660,f3289])).

fof(f4660,plain,
    ( r2_lattices(sK22,k7_lattices(sK22,sK23),sK23)
    | v2_struct_0(sK22)
    | ~ m1_subset_1(sK23,u1_struct_0(sK22)) ),
    inference(subsumption_resolution,[],[f4659,f3290])).

fof(f3290,plain,(
    v10_lattices(sK22) ),
    inference(cnf_transformation,[],[f2819])).

fof(f4659,plain,
    ( r2_lattices(sK22,k7_lattices(sK22,sK23),sK23)
    | ~ v10_lattices(sK22)
    | v2_struct_0(sK22)
    | ~ m1_subset_1(sK23,u1_struct_0(sK22)) ),
    inference(subsumption_resolution,[],[f4658,f4435])).

fof(f4435,plain,(
    v11_lattices(sK22) ),
    inference(subsumption_resolution,[],[f4434,f3292])).

fof(f4434,plain,
    ( v11_lattices(sK22)
    | ~ l3_lattices(sK22) ),
    inference(subsumption_resolution,[],[f4431,f3289])).

fof(f4431,plain,
    ( v11_lattices(sK22)
    | v2_struct_0(sK22)
    | ~ l3_lattices(sK22) ),
    inference(resolution,[],[f3291,f3437])).

fof(f3437,plain,(
    ! [X0] :
      ( ~ v17_lattices(X0)
      | v11_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f2207])).

fof(f2207,plain,(
    ! [X0] :
      ( ( v16_lattices(X0)
        & v15_lattices(X0)
        & v11_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f2206])).

fof(f2206,plain,(
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

fof(f3291,plain,(
    v17_lattices(sK22) ),
    inference(cnf_transformation,[],[f2819])).

fof(f4658,plain,
    ( r2_lattices(sK22,k7_lattices(sK22,sK23),sK23)
    | ~ v11_lattices(sK22)
    | ~ v10_lattices(sK22)
    | v2_struct_0(sK22)
    | ~ m1_subset_1(sK23,u1_struct_0(sK22)) ),
    inference(subsumption_resolution,[],[f4657,f4439])).

fof(f4439,plain,(
    v16_lattices(sK22) ),
    inference(subsumption_resolution,[],[f4438,f3292])).

fof(f4438,plain,
    ( v16_lattices(sK22)
    | ~ l3_lattices(sK22) ),
    inference(subsumption_resolution,[],[f4433,f3289])).

fof(f4433,plain,
    ( v16_lattices(sK22)
    | v2_struct_0(sK22)
    | ~ l3_lattices(sK22) ),
    inference(resolution,[],[f3291,f3439])).

fof(f3439,plain,(
    ! [X0] :
      ( ~ v17_lattices(X0)
      | v16_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f2207])).

fof(f4657,plain,
    ( r2_lattices(sK22,k7_lattices(sK22,sK23),sK23)
    | ~ v16_lattices(sK22)
    | ~ v11_lattices(sK22)
    | ~ v10_lattices(sK22)
    | v2_struct_0(sK22)
    | ~ m1_subset_1(sK23,u1_struct_0(sK22)) ),
    inference(subsumption_resolution,[],[f4622,f3292])).

fof(f4622,plain,
    ( r2_lattices(sK22,k7_lattices(sK22,sK23),sK23)
    | ~ l3_lattices(sK22)
    | ~ v16_lattices(sK22)
    | ~ v11_lattices(sK22)
    | ~ v10_lattices(sK22)
    | v2_struct_0(sK22)
    | ~ m1_subset_1(sK23,u1_struct_0(sK22)) ),
    inference(resolution,[],[f4528,f4413])).

fof(f4413,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | r2_lattices(X0,k7_lattices(X0,X1),X1)
      | ~ l3_lattices(X0)
      | ~ v16_lattices(X0)
      | ~ v11_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f4323])).

fof(f4323,plain,(
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
    inference(equality_resolution,[],[f3356])).

fof(f3356,plain,(
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
    inference(cnf_transformation,[],[f2861])).

fof(f2861,plain,(
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
    inference(nnf_transformation,[],[f2148])).

fof(f2148,plain,(
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
    inference(flattening,[],[f2147])).

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

fof(f5920,plain,(
    k4_lattices(sK22,k7_lattices(sK22,sK23),sK23) = k2_lattices(sK22,k7_lattices(sK22,sK23),sK23) ),
    inference(resolution,[],[f4499,f4528])).

fof(f4499,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK22))
      | k4_lattices(sK22,X1,sK23) = k2_lattices(sK22,X1,sK23) ) ),
    inference(subsumption_resolution,[],[f4498,f3289])).

fof(f4498,plain,(
    ! [X1] :
      ( k4_lattices(sK22,X1,sK23) = k2_lattices(sK22,X1,sK23)
      | ~ m1_subset_1(X1,u1_struct_0(sK22))
      | v2_struct_0(sK22) ) ),
    inference(subsumption_resolution,[],[f4497,f4456])).

fof(f4456,plain,(
    v6_lattices(sK22) ),
    inference(resolution,[],[f4422,f3445])).

fof(f3445,plain,(
    ! [X0] :
      ( ~ sP2(X0)
      | v6_lattices(X0) ) ),
    inference(cnf_transformation,[],[f2899])).

fof(f2899,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ sP2(X0) ) ),
    inference(nnf_transformation,[],[f2782])).

fof(f2782,plain,(
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

fof(f4422,plain,(
    sP2(sK22) ),
    inference(subsumption_resolution,[],[f4421,f3292])).

fof(f4421,plain,
    ( sP2(sK22)
    | ~ l3_lattices(sK22) ),
    inference(subsumption_resolution,[],[f4416,f3289])).

fof(f4416,plain,
    ( sP2(sK22)
    | v2_struct_0(sK22)
    | ~ l3_lattices(sK22) ),
    inference(resolution,[],[f3290,f3449])).

fof(f3449,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | sP2(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f2783])).

fof(f2783,plain,(
    ! [X0] :
      ( sP2(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(definition_folding,[],[f2213,f2782])).

fof(f2213,plain,(
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
    inference(flattening,[],[f2212])).

fof(f2212,plain,(
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

fof(f4497,plain,(
    ! [X1] :
      ( k4_lattices(sK22,X1,sK23) = k2_lattices(sK22,X1,sK23)
      | ~ m1_subset_1(X1,u1_struct_0(sK22))
      | ~ v6_lattices(sK22)
      | v2_struct_0(sK22) ) ),
    inference(subsumption_resolution,[],[f4461,f4447])).

fof(f4447,plain,(
    l1_lattices(sK22) ),
    inference(resolution,[],[f3292,f3432])).

fof(f3432,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | l1_lattices(X0) ) ),
    inference(cnf_transformation,[],[f2203])).

fof(f2203,plain,(
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

fof(f4461,plain,(
    ! [X1] :
      ( k4_lattices(sK22,X1,sK23) = k2_lattices(sK22,X1,sK23)
      | ~ m1_subset_1(X1,u1_struct_0(sK22))
      | ~ l1_lattices(sK22)
      | ~ v6_lattices(sK22)
      | v2_struct_0(sK22) ) ),
    inference(resolution,[],[f3293,f3331])).

fof(f3331,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2124])).

fof(f2124,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2123])).

fof(f2123,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2049])).

fof(f2049,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_lattices)).
%------------------------------------------------------------------------------
