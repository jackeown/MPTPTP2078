%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1641+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:28 EST 2020

% Result     : Theorem 1.87s
% Output     : Refutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 321 expanded)
%              Number of leaves         :   10 ( 119 expanded)
%              Depth                    :   13
%              Number of atoms          :  236 (1973 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3868,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3866,f3561])).

fof(f3561,plain,(
    ~ r1_orders_2(sK0,sK4(k5_waybel_0(sK0,sK1),k5_waybel_0(sK0,sK2)),sK2) ),
    inference(subsumption_resolution,[],[f3560,f3319])).

fof(f3319,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f3276])).

fof(f3276,plain,
    ( ~ r1_tarski(k5_waybel_0(sK0,sK1),k5_waybel_0(sK0,sK2))
    & r1_orders_2(sK0,sK1,sK2)
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v4_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f3225,f3275,f3274,f3273])).

fof(f3273,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k5_waybel_0(X0,X1),k5_waybel_0(X0,X2))
                & r1_orders_2(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_waybel_0(sK0,X1),k5_waybel_0(sK0,X2))
              & r1_orders_2(sK0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v4_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f3274,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k5_waybel_0(sK0,X1),k5_waybel_0(sK0,X2))
            & r1_orders_2(sK0,X1,X2)
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ~ r1_tarski(k5_waybel_0(sK0,sK1),k5_waybel_0(sK0,X2))
          & r1_orders_2(sK0,sK1,X2)
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f3275,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k5_waybel_0(sK0,sK1),k5_waybel_0(sK0,X2))
        & r1_orders_2(sK0,sK1,X2)
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ~ r1_tarski(k5_waybel_0(sK0,sK1),k5_waybel_0(sK0,sK2))
      & r1_orders_2(sK0,sK1,sK2)
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f3225,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_waybel_0(X0,X1),k5_waybel_0(X0,X2))
              & r1_orders_2(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3224])).

fof(f3224,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_waybel_0(X0,X1),k5_waybel_0(X0,X2))
              & r1_orders_2(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3203])).

fof(f3203,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r1_orders_2(X0,X1,X2)
                 => r1_tarski(k5_waybel_0(X0,X1),k5_waybel_0(X0,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f3202])).

fof(f3202,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
               => r1_tarski(k5_waybel_0(X0,X1),k5_waybel_0(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_waybel_0)).

fof(f3560,plain,
    ( ~ r1_orders_2(sK0,sK4(k5_waybel_0(sK0,sK1),k5_waybel_0(sK0,sK2)),sK2)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3559,f3321])).

fof(f3321,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f3276])).

fof(f3559,plain,
    ( ~ r1_orders_2(sK0,sK4(k5_waybel_0(sK0,sK1),k5_waybel_0(sK0,sK2)),sK2)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3558,f3323])).

fof(f3323,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f3276])).

fof(f3558,plain,
    ( ~ r1_orders_2(sK0,sK4(k5_waybel_0(sK0,sK1),k5_waybel_0(sK0,sK2)),sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3557,f3523])).

fof(f3523,plain,(
    m1_subset_1(sK4(k5_waybel_0(sK0,sK1),k5_waybel_0(sK0,sK2)),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f3421,f3431,f3364])).

fof(f3364,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f3256])).

fof(f3256,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f3255])).

fof(f3255,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f3431,plain,(
    r2_hidden(sK4(k5_waybel_0(sK0,sK1),k5_waybel_0(sK0,sK2)),k5_waybel_0(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f3325,f3340])).

fof(f3340,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3285])).

fof(f3285,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f3283,f3284])).

fof(f3284,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f3283,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f3282])).

fof(f3282,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3236])).

fof(f3236,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f3325,plain,(
    ~ r1_tarski(k5_waybel_0(sK0,sK1),k5_waybel_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f3276])).

fof(f3421,plain,(
    m1_subset_1(k5_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f3319,f3321,f3322,f3351])).

fof(f3351,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3243])).

fof(f3243,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3242])).

fof(f3242,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_waybel_0)).

fof(f3322,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f3276])).

fof(f3557,plain,
    ( ~ r1_orders_2(sK0,sK4(k5_waybel_0(sK0,sK1),k5_waybel_0(sK0,sK2)),sK2)
    | ~ m1_subset_1(sK4(k5_waybel_0(sK0,sK1),k5_waybel_0(sK0,sK2)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f3432,f3353])).

fof(f3353,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k5_waybel_0(X0,X1))
      | ~ r1_orders_2(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3292])).

fof(f3292,plain,(
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
    inference(nnf_transformation,[],[f3245])).

fof(f3245,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k5_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X2,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3244])).

fof(f3244,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k5_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X2,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3197])).

fof(f3197,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k5_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_waybel_0)).

fof(f3432,plain,(
    ~ r2_hidden(sK4(k5_waybel_0(sK0,sK1),k5_waybel_0(sK0,sK2)),k5_waybel_0(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f3325,f3341])).

fof(f3341,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3285])).

fof(f3866,plain,(
    r1_orders_2(sK0,sK4(k5_waybel_0(sK0,sK1),k5_waybel_0(sK0,sK2)),sK2) ),
    inference(unit_resulting_resolution,[],[f3320,f3321,f3324,f3323,f3322,f3523,f3538,f3355])).

fof(f3355,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3249])).

fof(f3249,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X1,X3)
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(flattening,[],[f3248])).

fof(f3248,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X1,X3)
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1954])).

fof(f1954,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X2) )
                   => r1_orders_2(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_orders_2)).

fof(f3538,plain,(
    r1_orders_2(sK0,sK4(k5_waybel_0(sK0,sK1),k5_waybel_0(sK0,sK2)),sK1) ),
    inference(subsumption_resolution,[],[f3537,f3319])).

fof(f3537,plain,
    ( r1_orders_2(sK0,sK4(k5_waybel_0(sK0,sK1),k5_waybel_0(sK0,sK2)),sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3536,f3321])).

fof(f3536,plain,
    ( r1_orders_2(sK0,sK4(k5_waybel_0(sK0,sK1),k5_waybel_0(sK0,sK2)),sK1)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3535,f3322])).

fof(f3535,plain,
    ( r1_orders_2(sK0,sK4(k5_waybel_0(sK0,sK1),k5_waybel_0(sK0,sK2)),sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3531,f3523])).

fof(f3531,plain,
    ( r1_orders_2(sK0,sK4(k5_waybel_0(sK0,sK1),k5_waybel_0(sK0,sK2)),sK1)
    | ~ m1_subset_1(sK4(k5_waybel_0(sK0,sK1),k5_waybel_0(sK0,sK2)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f3431,f3352])).

fof(f3352,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k5_waybel_0(X0,X1))
      | r1_orders_2(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3292])).

fof(f3324,plain,(
    r1_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f3276])).

fof(f3320,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f3276])).
%------------------------------------------------------------------------------
