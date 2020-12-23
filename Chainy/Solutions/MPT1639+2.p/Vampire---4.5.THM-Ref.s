%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1639+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:27 EST 2020

% Result     : Theorem 1.87s
% Output     : Refutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 340 expanded)
%              Number of leaves         :    9 ( 125 expanded)
%              Depth                    :   18
%              Number of atoms          :  273 (2397 expanded)
%              Number of equality atoms :   33 ( 650 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3400,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3399,f3395])).

fof(f3395,plain,(
    ~ r1_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f3394,f3268])).

fof(f3268,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f3242])).

fof(f3242,plain,
    ( sK1 != sK2
    & k5_waybel_0(sK0,sK1) = k5_waybel_0(sK0,sK2)
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f3212,f3241,f3240,f3239])).

fof(f3239,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( X1 != X2
                & k5_waybel_0(X0,X1) = k5_waybel_0(X0,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k5_waybel_0(sK0,X1) = k5_waybel_0(sK0,X2)
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f3240,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( X1 != X2
            & k5_waybel_0(sK0,X1) = k5_waybel_0(sK0,X2)
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( sK1 != X2
          & k5_waybel_0(sK0,X2) = k5_waybel_0(sK0,sK1)
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f3241,plain,
    ( ? [X2] :
        ( sK1 != X2
        & k5_waybel_0(sK0,X2) = k5_waybel_0(sK0,sK1)
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( sK1 != sK2
      & k5_waybel_0(sK0,sK1) = k5_waybel_0(sK0,sK2)
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f3212,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k5_waybel_0(X0,X1) = k5_waybel_0(X0,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3211])).

fof(f3211,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k5_waybel_0(X0,X1) = k5_waybel_0(X0,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3199])).

fof(f3199,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( k5_waybel_0(X0,X1) = k5_waybel_0(X0,X2)
                 => X1 = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f3198])).

fof(f3198,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( k5_waybel_0(X0,X1) = k5_waybel_0(X0,X2)
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_waybel_0)).

fof(f3394,plain,
    ( ~ r1_orders_2(sK0,sK1,sK2)
    | sK1 = sK2 ),
    inference(subsumption_resolution,[],[f3393,f3265])).

fof(f3265,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f3242])).

fof(f3393,plain,
    ( ~ r1_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | sK1 = sK2 ),
    inference(subsumption_resolution,[],[f3391,f3266])).

fof(f3266,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f3242])).

fof(f3391,plain,
    ( ~ r1_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | sK1 = sK2 ),
    inference(resolution,[],[f3389,f3298])).

fof(f3298,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK0,X0,X1)
      | ~ r1_orders_2(sK0,X1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | X0 = X1 ) ),
    inference(global_subsumption,[],[f3264,f3297])).

fof(f3297,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK0,X0,X1)
      | ~ r1_orders_2(sK0,X1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | X0 = X1 ) ),
    inference(resolution,[],[f3263,f3292])).

fof(f3292,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ r1_orders_2(X0,X2,X1)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f3236])).

fof(f3236,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f3235])).

fof(f3235,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1953])).

fof(f1953,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r1_orders_2(X0,X2,X1)
                  & r1_orders_2(X0,X1,X2) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_orders_2)).

fof(f3263,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f3242])).

fof(f3264,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f3242])).

fof(f3389,plain,(
    r1_orders_2(sK0,sK2,sK1) ),
    inference(resolution,[],[f3381,f3339])).

fof(f3339,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k5_waybel_0(sK0,sK1))
      | r1_orders_2(sK0,X0,sK1) ) ),
    inference(global_subsumption,[],[f3320,f3336])).

fof(f3336,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,k5_waybel_0(sK0,sK1))
      | r1_orders_2(sK0,X0,sK1) ) ),
    inference(resolution,[],[f3304,f3265])).

fof(f3304,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X1,k5_waybel_0(sK0,X2))
      | r1_orders_2(sK0,X1,X2) ) ),
    inference(subsumption_resolution,[],[f3300,f3261])).

fof(f3261,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f3242])).

fof(f3300,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X1,k5_waybel_0(sK0,X2))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r1_orders_2(sK0,X1,X2)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f3264,f3281])).

fof(f3281,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_hidden(X2,k5_waybel_0(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(X0,X2,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3256])).

fof(f3256,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k5_waybel_0(X0,X1))
                  | ~ r1_orders_2(X0,X2,X1) )
                & ( r1_orders_2(X0,X2,X1)
                  | ~ r2_hidden(X2,k5_waybel_0(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3224])).

fof(f3224,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k5_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X2,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3223])).

fof(f3223,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k5_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X2,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3196])).

fof(f3196,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k5_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_waybel_0)).

fof(f3320,plain,(
    ! [X3] :
      ( m1_subset_1(X3,u1_struct_0(sK0))
      | ~ r2_hidden(X3,k5_waybel_0(sK0,sK1)) ) ),
    inference(resolution,[],[f3308,f3284])).

fof(f3284,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f3228])).

fof(f3228,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f3227])).

fof(f3227,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f618])).

fof(f618,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f3308,plain,(
    m1_subset_1(k5_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f3306,f3265])).

fof(f3306,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,u1_struct_0(sK0))
      | m1_subset_1(k5_waybel_0(sK0,X5),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f3302,f3261])).

fof(f3302,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,u1_struct_0(sK0))
      | m1_subset_1(k5_waybel_0(sK0,X5),k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f3264,f3280])).

fof(f3280,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3222])).

fof(f3222,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3221])).

fof(f3221,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3170])).

fof(f3170,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_waybel_0)).

fof(f3381,plain,(
    r2_hidden(sK2,k5_waybel_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f3379,f3267])).

fof(f3267,plain,(
    k5_waybel_0(sK0,sK1) = k5_waybel_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f3242])).

fof(f3379,plain,(
    r2_hidden(sK2,k5_waybel_0(sK0,sK2)) ),
    inference(resolution,[],[f3364,f3266])).

fof(f3364,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,k5_waybel_0(sK0,X0)) ) ),
    inference(duplicate_literal_removal,[],[f3363])).

fof(f3363,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,k5_waybel_0(sK0,X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f3305,f3296])).

fof(f3296,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,X0,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(global_subsumption,[],[f3264,f3295])).

fof(f3295,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | r1_orders_2(sK0,X0,X0) ) ),
    inference(subsumption_resolution,[],[f3294,f3261])).

fof(f3294,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | r1_orders_2(sK0,X0,X0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f3262,f3293])).

fof(f3293,plain,(
    ! [X0,X1] :
      ( ~ v3_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X1,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3238])).

fof(f3238,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3237])).

fof(f3237,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1952])).

fof(f1952,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,X1,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_orders_2)).

fof(f3262,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f3242])).

fof(f3305,plain,(
    ! [X4,X3] :
      ( ~ r1_orders_2(sK0,X3,X4)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | r2_hidden(X3,k5_waybel_0(sK0,X4)) ) ),
    inference(subsumption_resolution,[],[f3301,f3261])).

fof(f3301,plain,(
    ! [X4,X3] :
      ( ~ r1_orders_2(sK0,X3,X4)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | r2_hidden(X3,k5_waybel_0(sK0,X4))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f3264,f3282])).

fof(f3282,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r2_hidden(X2,k5_waybel_0(X0,X1))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3256])).

fof(f3399,plain,(
    r1_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f3396,f3378])).

fof(f3378,plain,(
    r2_hidden(sK1,k5_waybel_0(sK0,sK1)) ),
    inference(resolution,[],[f3364,f3265])).

fof(f3396,plain,
    ( ~ r2_hidden(sK1,k5_waybel_0(sK0,sK1))
    | r1_orders_2(sK0,sK1,sK2) ),
    inference(resolution,[],[f3340,f3265])).

fof(f3340,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X1,k5_waybel_0(sK0,sK1))
      | r1_orders_2(sK0,X1,sK2) ) ),
    inference(forward_demodulation,[],[f3337,f3267])).

fof(f3337,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X1,k5_waybel_0(sK0,sK2))
      | r1_orders_2(sK0,X1,sK2) ) ),
    inference(resolution,[],[f3304,f3266])).
%------------------------------------------------------------------------------
