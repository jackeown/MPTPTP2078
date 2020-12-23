%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1213+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:12 EST 2020

% Result     : Theorem 11.59s
% Output     : Refutation 11.83s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 730 expanded)
%              Number of leaves         :    5 ( 126 expanded)
%              Depth                    :   21
%              Number of atoms          :  382 (3594 expanded)
%              Number of equality atoms :   79 ( 522 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6039,plain,(
    $false ),
    inference(subsumption_resolution,[],[f6038,f4937])).

fof(f4937,plain,(
    ~ r2_lattices(sK0,sK1,k7_lattices(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f4936,f2327])).

fof(f2327,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f2079])).

fof(f2079,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k7_lattices(X0,k7_lattices(X0,X1)) != X1
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f2078])).

fof(f2078,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k7_lattices(X0,k7_lattices(X0,X1)) != X1
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2074])).

fof(f2074,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v17_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => k7_lattices(X0,k7_lattices(X0,X1)) = X1 ) ) ),
    inference(negated_conjecture,[],[f2073])).

fof(f2073,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k7_lattices(X0,k7_lattices(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_lattices)).

fof(f4936,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r2_lattices(sK0,sK1,k7_lattices(sK0,sK1)) ),
    inference(equality_resolution,[],[f3175])).

fof(f3175,plain,(
    ! [X0] :
      ( sK1 != X0
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_lattices(sK0,X0,k7_lattices(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f3174,f2332])).

fof(f2332,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f2079])).

fof(f3174,plain,(
    ! [X0] :
      ( sK1 != X0
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_lattices(sK0,X0,k7_lattices(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f3173,f2812])).

fof(f2812,plain,(
    v16_lattices(sK0) ),
    inference(subsumption_resolution,[],[f2811,f2331])).

fof(f2331,plain,(
    v17_lattices(sK0) ),
    inference(cnf_transformation,[],[f2079])).

fof(f2811,plain,
    ( ~ v17_lattices(sK0)
    | v16_lattices(sK0) ),
    inference(subsumption_resolution,[],[f2747,f2332])).

fof(f2747,plain,
    ( ~ l3_lattices(sK0)
    | ~ v17_lattices(sK0)
    | v16_lattices(sK0) ),
    inference(resolution,[],[f2329,f2381])).

fof(f2381,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ v17_lattices(X0)
      | v16_lattices(X0) ) ),
    inference(cnf_transformation,[],[f2119])).

fof(f2119,plain,(
    ! [X0] :
      ( ( v16_lattices(X0)
        & v15_lattices(X0)
        & v11_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f2118])).

fof(f2118,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_lattices)).

fof(f2329,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f2079])).

fof(f3173,plain,(
    ! [X0] :
      ( sK1 != X0
      | ~ v16_lattices(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_lattices(sK0,X0,k7_lattices(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f3172,f2808])).

fof(f2808,plain,(
    v11_lattices(sK0) ),
    inference(subsumption_resolution,[],[f2807,f2331])).

fof(f2807,plain,
    ( ~ v17_lattices(sK0)
    | v11_lattices(sK0) ),
    inference(subsumption_resolution,[],[f2745,f2332])).

fof(f2745,plain,
    ( ~ l3_lattices(sK0)
    | ~ v17_lattices(sK0)
    | v11_lattices(sK0) ),
    inference(resolution,[],[f2329,f2379])).

fof(f2379,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ v17_lattices(X0)
      | v11_lattices(X0) ) ),
    inference(cnf_transformation,[],[f2119])).

fof(f3172,plain,(
    ! [X0] :
      ( sK1 != X0
      | ~ v11_lattices(sK0)
      | ~ v16_lattices(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_lattices(sK0,X0,k7_lattices(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f3171,f2330])).

fof(f2330,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f2079])).

fof(f3171,plain,(
    ! [X0] :
      ( sK1 != X0
      | ~ v10_lattices(sK0)
      | ~ v11_lattices(sK0)
      | ~ v16_lattices(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_lattices(sK0,X0,k7_lattices(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f3170,f2329])).

fof(f3170,plain,(
    ! [X0] :
      ( sK1 != X0
      | v2_struct_0(sK0)
      | ~ v10_lattices(sK0)
      | ~ v11_lattices(sK0)
      | ~ v16_lattices(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_lattices(sK0,X0,k7_lattices(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f3163,f3007])).

fof(f3007,plain,(
    m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f3006,f2332])).

fof(f3006,plain,
    ( ~ l3_lattices(sK0)
    | m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f2939,f2329])).

fof(f2939,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f2327,f2351])).

fof(f2351,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f2089])).

fof(f2089,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2088])).

fof(f2088,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_lattices)).

fof(f3163,plain,(
    ! [X0] :
      ( sK1 != X0
      | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | ~ v10_lattices(sK0)
      | ~ v11_lattices(sK0)
      | ~ v16_lattices(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_lattices(sK0,X0,k7_lattices(sK0,sK1)) ) ),
    inference(superposition,[],[f2328,f2354])).

fof(f2354,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v11_lattices(X0)
      | ~ v16_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_lattices(X0,X2,X1)
      | k7_lattices(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2095])).

fof(f2095,plain,(
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
    inference(flattening,[],[f2094])).

fof(f2094,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d21_lattices)).

fof(f2328,plain,(
    sK1 != k7_lattices(sK0,k7_lattices(sK0,sK1)) ),
    inference(cnf_transformation,[],[f2079])).

fof(f6038,plain,(
    r2_lattices(sK0,sK1,k7_lattices(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f6037,f3519])).

fof(f3519,plain,(
    k5_lattices(sK0) = k2_lattices(sK0,k7_lattices(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f3518,f2327])).

fof(f3518,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | k5_lattices(sK0) = k2_lattices(sK0,k7_lattices(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f3517,f3007])).

fof(f3517,plain,
    ( ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | k5_lattices(sK0) = k2_lattices(sK0,k7_lattices(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f3516,f2332])).

fof(f3516,plain,
    ( ~ l3_lattices(sK0)
    | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | k5_lattices(sK0) = k2_lattices(sK0,k7_lattices(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f3504,f2329])).

fof(f3504,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | k5_lattices(sK0) = k2_lattices(sK0,k7_lattices(sK0,sK1),sK1) ),
    inference(resolution,[],[f3149,f2575])).

fof(f2575,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k2_lattices(X0,X1,X2) = k5_lattices(X0)
      | ~ r2_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f2267])).

fof(f2267,plain,(
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
    inference(flattening,[],[f2266])).

fof(f2266,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_lattices)).

fof(f3149,plain,(
    r2_lattices(sK0,k7_lattices(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f3148,f3007])).

fof(f3148,plain,
    ( ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | r2_lattices(sK0,k7_lattices(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f3147,f2332])).

fof(f3147,plain,
    ( ~ l3_lattices(sK0)
    | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | r2_lattices(sK0,k7_lattices(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f3146,f2812])).

fof(f3146,plain,
    ( ~ v16_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | r2_lattices(sK0,k7_lattices(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f3145,f2808])).

fof(f3145,plain,
    ( ~ v11_lattices(sK0)
    | ~ v16_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | r2_lattices(sK0,k7_lattices(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f3144,f2330])).

fof(f3144,plain,
    ( ~ v10_lattices(sK0)
    | ~ v11_lattices(sK0)
    | ~ v16_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | r2_lattices(sK0,k7_lattices(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f2997,f2329])).

fof(f2997,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ v11_lattices(sK0)
    | ~ v16_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | r2_lattices(sK0,k7_lattices(sK0,sK1),sK1) ),
    inference(resolution,[],[f2327,f2713])).

fof(f2713,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v11_lattices(X0)
      | ~ v16_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | r2_lattices(X0,k7_lattices(X0,X1),X1) ) ),
    inference(equality_resolution,[],[f2355])).

fof(f2355,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v11_lattices(X0)
      | ~ v16_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_lattices(X0,X2,X1)
      | k7_lattices(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2095])).

fof(f6037,plain,
    ( k5_lattices(sK0) != k2_lattices(sK0,k7_lattices(sK0,sK1),sK1)
    | r2_lattices(sK0,sK1,k7_lattices(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f6036,f3523])).

fof(f3523,plain,(
    k5_lattices(sK0) = k2_lattices(sK0,sK1,k7_lattices(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f3522,f2327])).

fof(f3522,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | k5_lattices(sK0) = k2_lattices(sK0,sK1,k7_lattices(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f3521,f3007])).

fof(f3521,plain,
    ( ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | k5_lattices(sK0) = k2_lattices(sK0,sK1,k7_lattices(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f3520,f2332])).

fof(f3520,plain,
    ( ~ l3_lattices(sK0)
    | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | k5_lattices(sK0) = k2_lattices(sK0,sK1,k7_lattices(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f3505,f2329])).

fof(f3505,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | k5_lattices(sK0) = k2_lattices(sK0,sK1,k7_lattices(sK0,sK1)) ),
    inference(resolution,[],[f3149,f2576])).

fof(f2576,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k5_lattices(X0) = k2_lattices(X0,X2,X1)
      | ~ r2_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f2267])).

fof(f6036,plain,
    ( k5_lattices(sK0) != k2_lattices(sK0,sK1,k7_lattices(sK0,sK1))
    | k5_lattices(sK0) != k2_lattices(sK0,k7_lattices(sK0,sK1),sK1)
    | r2_lattices(sK0,sK1,k7_lattices(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f6035,f3511])).

fof(f3511,plain,(
    k6_lattices(sK0) = k1_lattices(sK0,k7_lattices(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f3510,f2327])).

fof(f3510,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | k6_lattices(sK0) = k1_lattices(sK0,k7_lattices(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f3509,f3007])).

fof(f3509,plain,
    ( ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | k6_lattices(sK0) = k1_lattices(sK0,k7_lattices(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f3508,f2332])).

fof(f3508,plain,
    ( ~ l3_lattices(sK0)
    | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | k6_lattices(sK0) = k1_lattices(sK0,k7_lattices(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f3502,f2329])).

fof(f3502,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | k6_lattices(sK0) = k1_lattices(sK0,k7_lattices(sK0,sK1),sK1) ),
    inference(resolution,[],[f3149,f2573])).

fof(f2573,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k6_lattices(X0) = k1_lattices(X0,X1,X2)
      | ~ r2_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f2267])).

fof(f6035,plain,
    ( k6_lattices(sK0) != k1_lattices(sK0,k7_lattices(sK0,sK1),sK1)
    | k5_lattices(sK0) != k2_lattices(sK0,sK1,k7_lattices(sK0,sK1))
    | k5_lattices(sK0) != k2_lattices(sK0,k7_lattices(sK0,sK1),sK1)
    | r2_lattices(sK0,sK1,k7_lattices(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f5998,f3515])).

fof(f3515,plain,(
    k6_lattices(sK0) = k1_lattices(sK0,sK1,k7_lattices(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f3514,f2327])).

fof(f3514,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | k6_lattices(sK0) = k1_lattices(sK0,sK1,k7_lattices(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f3513,f3007])).

fof(f3513,plain,
    ( ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | k6_lattices(sK0) = k1_lattices(sK0,sK1,k7_lattices(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f3512,f2332])).

fof(f3512,plain,
    ( ~ l3_lattices(sK0)
    | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | k6_lattices(sK0) = k1_lattices(sK0,sK1,k7_lattices(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f3503,f2329])).

fof(f3503,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | k6_lattices(sK0) = k1_lattices(sK0,sK1,k7_lattices(sK0,sK1)) ),
    inference(resolution,[],[f3149,f2574])).

fof(f2574,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k6_lattices(X0) = k1_lattices(X0,X2,X1)
      | ~ r2_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f2267])).

fof(f5998,plain,
    ( k6_lattices(sK0) != k1_lattices(sK0,sK1,k7_lattices(sK0,sK1))
    | k6_lattices(sK0) != k1_lattices(sK0,k7_lattices(sK0,sK1),sK1)
    | k5_lattices(sK0) != k2_lattices(sK0,sK1,k7_lattices(sK0,sK1))
    | k5_lattices(sK0) != k2_lattices(sK0,k7_lattices(sK0,sK1),sK1)
    | r2_lattices(sK0,sK1,k7_lattices(sK0,sK1)) ),
    inference(resolution,[],[f3132,f3007])).

fof(f3132,plain,(
    ! [X54] :
      ( ~ m1_subset_1(X54,u1_struct_0(sK0))
      | k6_lattices(sK0) != k1_lattices(sK0,sK1,X54)
      | k6_lattices(sK0) != k1_lattices(sK0,X54,sK1)
      | k5_lattices(sK0) != k2_lattices(sK0,sK1,X54)
      | k5_lattices(sK0) != k2_lattices(sK0,X54,sK1)
      | r2_lattices(sK0,sK1,X54) ) ),
    inference(subsumption_resolution,[],[f3131,f2332])).

fof(f3131,plain,(
    ! [X54] :
      ( ~ l3_lattices(sK0)
      | ~ m1_subset_1(X54,u1_struct_0(sK0))
      | k6_lattices(sK0) != k1_lattices(sK0,sK1,X54)
      | k6_lattices(sK0) != k1_lattices(sK0,X54,sK1)
      | k5_lattices(sK0) != k2_lattices(sK0,sK1,X54)
      | k5_lattices(sK0) != k2_lattices(sK0,X54,sK1)
      | r2_lattices(sK0,sK1,X54) ) ),
    inference(subsumption_resolution,[],[f2992,f2329])).

fof(f2992,plain,(
    ! [X54] :
      ( v2_struct_0(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(X54,u1_struct_0(sK0))
      | k6_lattices(sK0) != k1_lattices(sK0,sK1,X54)
      | k6_lattices(sK0) != k1_lattices(sK0,X54,sK1)
      | k5_lattices(sK0) != k2_lattices(sK0,sK1,X54)
      | k5_lattices(sK0) != k2_lattices(sK0,X54,sK1)
      | r2_lattices(sK0,sK1,X54) ) ),
    inference(resolution,[],[f2327,f2577])).

fof(f2577,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k6_lattices(X0) != k1_lattices(X0,X1,X2)
      | k6_lattices(X0) != k1_lattices(X0,X2,X1)
      | k2_lattices(X0,X1,X2) != k5_lattices(X0)
      | k5_lattices(X0) != k2_lattices(X0,X2,X1)
      | r2_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f2267])).
%------------------------------------------------------------------------------
