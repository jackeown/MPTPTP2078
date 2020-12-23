%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1654+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:28 EST 2020

% Result     : Theorem 4.33s
% Output     : Refutation 4.33s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 388 expanded)
%              Number of leaves         :    9 ( 123 expanded)
%              Depth                    :   20
%              Number of atoms          :  323 (2745 expanded)
%              Number of equality atoms :   42 ( 382 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11482,plain,(
    $false ),
    inference(subsumption_resolution,[],[f11481,f11475])).

fof(f11475,plain,(
    ~ r1_yellow_0(sK80,k5_waybel_0(sK80,sK81)) ),
    inference(trivial_inequality_removal,[],[f11474])).

fof(f11474,plain,
    ( sK81 != sK81
    | ~ r1_yellow_0(sK80,k5_waybel_0(sK80,sK81)) ),
    inference(backward_demodulation,[],[f5698,f11472])).

fof(f11472,plain,(
    sK81 = k1_yellow_0(sK80,k5_waybel_0(sK80,sK81)) ),
    inference(forward_demodulation,[],[f11471,f8321])).

fof(f8321,plain,(
    sK81 = k1_yellow_0(sK80,k6_domain_1(u1_struct_0(sK80),sK81)) ),
    inference(subsumption_resolution,[],[f8320,f5692])).

fof(f5692,plain,(
    ~ v2_struct_0(sK80) ),
    inference(cnf_transformation,[],[f4652])).

fof(f4652,plain,
    ( ( sK81 != k1_yellow_0(sK80,k5_waybel_0(sK80,sK81))
      | ~ r1_yellow_0(sK80,k5_waybel_0(sK80,sK81)) )
    & m1_subset_1(sK81,u1_struct_0(sK80))
    & l1_orders_2(sK80)
    & v5_orders_2(sK80)
    & v4_orders_2(sK80)
    & v3_orders_2(sK80)
    & ~ v2_struct_0(sK80) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK80,sK81])],[f3301,f4651,f4650])).

fof(f4650,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k1_yellow_0(X0,k5_waybel_0(X0,X1)) != X1
              | ~ r1_yellow_0(X0,k5_waybel_0(X0,X1)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( k1_yellow_0(sK80,k5_waybel_0(sK80,X1)) != X1
            | ~ r1_yellow_0(sK80,k5_waybel_0(sK80,X1)) )
          & m1_subset_1(X1,u1_struct_0(sK80)) )
      & l1_orders_2(sK80)
      & v5_orders_2(sK80)
      & v4_orders_2(sK80)
      & v3_orders_2(sK80)
      & ~ v2_struct_0(sK80) ) ),
    introduced(choice_axiom,[])).

fof(f4651,plain,
    ( ? [X1] :
        ( ( k1_yellow_0(sK80,k5_waybel_0(sK80,X1)) != X1
          | ~ r1_yellow_0(sK80,k5_waybel_0(sK80,X1)) )
        & m1_subset_1(X1,u1_struct_0(sK80)) )
   => ( ( sK81 != k1_yellow_0(sK80,k5_waybel_0(sK80,sK81))
        | ~ r1_yellow_0(sK80,k5_waybel_0(sK80,sK81)) )
      & m1_subset_1(sK81,u1_struct_0(sK80)) ) ),
    introduced(choice_axiom,[])).

fof(f3301,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k1_yellow_0(X0,k5_waybel_0(X0,X1)) != X1
            | ~ r1_yellow_0(X0,k5_waybel_0(X0,X1)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3300])).

fof(f3300,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k1_yellow_0(X0,k5_waybel_0(X0,X1)) != X1
            | ~ r1_yellow_0(X0,k5_waybel_0(X0,X1)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3225])).

fof(f3225,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1
              & r1_yellow_0(X0,k5_waybel_0(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f3224])).

fof(f3224,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( k1_yellow_0(X0,k5_waybel_0(X0,X1)) = X1
            & r1_yellow_0(X0,k5_waybel_0(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_waybel_0)).

fof(f8320,plain,
    ( sK81 = k1_yellow_0(sK80,k6_domain_1(u1_struct_0(sK80),sK81))
    | v2_struct_0(sK80) ),
    inference(subsumption_resolution,[],[f8319,f5693])).

fof(f5693,plain,(
    v3_orders_2(sK80) ),
    inference(cnf_transformation,[],[f4652])).

fof(f8319,plain,
    ( sK81 = k1_yellow_0(sK80,k6_domain_1(u1_struct_0(sK80),sK81))
    | ~ v3_orders_2(sK80)
    | v2_struct_0(sK80) ),
    inference(subsumption_resolution,[],[f8318,f5695])).

fof(f5695,plain,(
    v5_orders_2(sK80) ),
    inference(cnf_transformation,[],[f4652])).

fof(f8318,plain,
    ( sK81 = k1_yellow_0(sK80,k6_domain_1(u1_struct_0(sK80),sK81))
    | ~ v5_orders_2(sK80)
    | ~ v3_orders_2(sK80)
    | v2_struct_0(sK80) ),
    inference(subsumption_resolution,[],[f8237,f5696])).

fof(f5696,plain,(
    l1_orders_2(sK80) ),
    inference(cnf_transformation,[],[f4652])).

fof(f8237,plain,
    ( sK81 = k1_yellow_0(sK80,k6_domain_1(u1_struct_0(sK80),sK81))
    | ~ l1_orders_2(sK80)
    | ~ v5_orders_2(sK80)
    | ~ v3_orders_2(sK80)
    | v2_struct_0(sK80) ),
    inference(resolution,[],[f5697,f5757])).

fof(f5757,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3341])).

fof(f3341,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
            & k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3340])).

fof(f3340,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
            & k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3035])).

fof(f3035,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( k2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
            & k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_yellow_0)).

fof(f5697,plain,(
    m1_subset_1(sK81,u1_struct_0(sK80)) ),
    inference(cnf_transformation,[],[f4652])).

fof(f11471,plain,(
    k1_yellow_0(sK80,k5_waybel_0(sK80,sK81)) = k1_yellow_0(sK80,k6_domain_1(u1_struct_0(sK80),sK81)) ),
    inference(forward_demodulation,[],[f11470,f8348])).

fof(f8348,plain,(
    k5_waybel_0(sK80,sK81) = k3_waybel_0(sK80,k6_domain_1(u1_struct_0(sK80),sK81)) ),
    inference(subsumption_resolution,[],[f8347,f5692])).

fof(f8347,plain,
    ( k5_waybel_0(sK80,sK81) = k3_waybel_0(sK80,k6_domain_1(u1_struct_0(sK80),sK81))
    | v2_struct_0(sK80) ),
    inference(subsumption_resolution,[],[f8246,f5696])).

fof(f8246,plain,
    ( k5_waybel_0(sK80,sK81) = k3_waybel_0(sK80,k6_domain_1(u1_struct_0(sK80),sK81))
    | ~ l1_orders_2(sK80)
    | v2_struct_0(sK80) ),
    inference(resolution,[],[f5697,f5854])).

fof(f5854,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | k5_waybel_0(X0,X1) = k3_waybel_0(X0,k6_domain_1(u1_struct_0(X0),X1))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3400])).

fof(f3400,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_waybel_0(X0,X1) = k3_waybel_0(X0,k6_domain_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3399])).

fof(f3399,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_waybel_0(X0,X1) = k3_waybel_0(X0,k6_domain_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3160])).

fof(f3160,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k5_waybel_0(X0,X1) = k3_waybel_0(X0,k6_domain_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_waybel_0)).

fof(f11470,plain,(
    k1_yellow_0(sK80,k6_domain_1(u1_struct_0(sK80),sK81)) = k1_yellow_0(sK80,k3_waybel_0(sK80,k6_domain_1(u1_struct_0(sK80),sK81))) ),
    inference(subsumption_resolution,[],[f11469,f5692])).

fof(f11469,plain,
    ( k1_yellow_0(sK80,k6_domain_1(u1_struct_0(sK80),sK81)) = k1_yellow_0(sK80,k3_waybel_0(sK80,k6_domain_1(u1_struct_0(sK80),sK81)))
    | v2_struct_0(sK80) ),
    inference(subsumption_resolution,[],[f11468,f5693])).

fof(f11468,plain,
    ( k1_yellow_0(sK80,k6_domain_1(u1_struct_0(sK80),sK81)) = k1_yellow_0(sK80,k3_waybel_0(sK80,k6_domain_1(u1_struct_0(sK80),sK81)))
    | ~ v3_orders_2(sK80)
    | v2_struct_0(sK80) ),
    inference(subsumption_resolution,[],[f11467,f5694])).

fof(f5694,plain,(
    v4_orders_2(sK80) ),
    inference(cnf_transformation,[],[f4652])).

fof(f11467,plain,
    ( k1_yellow_0(sK80,k6_domain_1(u1_struct_0(sK80),sK81)) = k1_yellow_0(sK80,k3_waybel_0(sK80,k6_domain_1(u1_struct_0(sK80),sK81)))
    | ~ v4_orders_2(sK80)
    | ~ v3_orders_2(sK80)
    | v2_struct_0(sK80) ),
    inference(subsumption_resolution,[],[f11466,f5696])).

fof(f11466,plain,
    ( k1_yellow_0(sK80,k6_domain_1(u1_struct_0(sK80),sK81)) = k1_yellow_0(sK80,k3_waybel_0(sK80,k6_domain_1(u1_struct_0(sK80),sK81)))
    | ~ l1_orders_2(sK80)
    | ~ v4_orders_2(sK80)
    | ~ v3_orders_2(sK80)
    | v2_struct_0(sK80) ),
    inference(subsumption_resolution,[],[f11350,f8331])).

fof(f8331,plain,(
    r1_yellow_0(sK80,k6_domain_1(u1_struct_0(sK80),sK81)) ),
    inference(subsumption_resolution,[],[f8330,f5692])).

fof(f8330,plain,
    ( r1_yellow_0(sK80,k6_domain_1(u1_struct_0(sK80),sK81))
    | v2_struct_0(sK80) ),
    inference(subsumption_resolution,[],[f8329,f5693])).

fof(f8329,plain,
    ( r1_yellow_0(sK80,k6_domain_1(u1_struct_0(sK80),sK81))
    | ~ v3_orders_2(sK80)
    | v2_struct_0(sK80) ),
    inference(subsumption_resolution,[],[f8328,f5695])).

fof(f8328,plain,
    ( r1_yellow_0(sK80,k6_domain_1(u1_struct_0(sK80),sK81))
    | ~ v5_orders_2(sK80)
    | ~ v3_orders_2(sK80)
    | v2_struct_0(sK80) ),
    inference(subsumption_resolution,[],[f8240,f5696])).

fof(f8240,plain,
    ( r1_yellow_0(sK80,k6_domain_1(u1_struct_0(sK80),sK81))
    | ~ l1_orders_2(sK80)
    | ~ v5_orders_2(sK80)
    | ~ v3_orders_2(sK80)
    | v2_struct_0(sK80) ),
    inference(resolution,[],[f5697,f5814])).

fof(f5814,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3376])).

fof(f3376,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1))
            & r1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3375])).

fof(f3375,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1))
            & r1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3034])).

fof(f3034,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( r2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1))
            & r1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_yellow_0)).

fof(f11350,plain,
    ( ~ r1_yellow_0(sK80,k6_domain_1(u1_struct_0(sK80),sK81))
    | k1_yellow_0(sK80,k6_domain_1(u1_struct_0(sK80),sK81)) = k1_yellow_0(sK80,k3_waybel_0(sK80,k6_domain_1(u1_struct_0(sK80),sK81)))
    | ~ l1_orders_2(sK80)
    | ~ v4_orders_2(sK80)
    | ~ v3_orders_2(sK80)
    | v2_struct_0(sK80) ),
    inference(resolution,[],[f8404,f5759])).

fof(f5759,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_yellow_0(X0,X1)
      | k1_yellow_0(X0,X1) = k1_yellow_0(X0,k3_waybel_0(X0,X1))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3343])).

fof(f3343,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_yellow_0(X0,X1) = k1_yellow_0(X0,k3_waybel_0(X0,X1))
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3342])).

fof(f3342,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_yellow_0(X0,X1) = k1_yellow_0(X0,k3_waybel_0(X0,X1))
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3223])).

fof(f3223,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r1_yellow_0(X0,X1)
           => k1_yellow_0(X0,X1) = k1_yellow_0(X0,k3_waybel_0(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_waybel_0)).

fof(f8404,plain,(
    m1_subset_1(k6_domain_1(u1_struct_0(sK80),sK81),k1_zfmisc_1(u1_struct_0(sK80))) ),
    inference(subsumption_resolution,[],[f8403,f5692])).

fof(f8403,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK80),sK81),k1_zfmisc_1(u1_struct_0(sK80)))
    | v2_struct_0(sK80) ),
    inference(subsumption_resolution,[],[f8402,f5693])).

fof(f8402,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK80),sK81),k1_zfmisc_1(u1_struct_0(sK80)))
    | ~ v3_orders_2(sK80)
    | v2_struct_0(sK80) ),
    inference(subsumption_resolution,[],[f8290,f5696])).

fof(f8290,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK80),sK81),k1_zfmisc_1(u1_struct_0(sK80)))
    | ~ l1_orders_2(sK80)
    | ~ v3_orders_2(sK80)
    | v2_struct_0(sK80) ),
    inference(resolution,[],[f5697,f7109])).

fof(f7109,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4071])).

fof(f4071,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f4070])).

fof(f4070,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1961])).

fof(f1961,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_orders_2)).

fof(f5698,plain,
    ( sK81 != k1_yellow_0(sK80,k5_waybel_0(sK80,sK81))
    | ~ r1_yellow_0(sK80,k5_waybel_0(sK80,sK81)) ),
    inference(cnf_transformation,[],[f4652])).

fof(f11481,plain,(
    r1_yellow_0(sK80,k5_waybel_0(sK80,sK81)) ),
    inference(forward_demodulation,[],[f11480,f8348])).

fof(f11480,plain,(
    r1_yellow_0(sK80,k3_waybel_0(sK80,k6_domain_1(u1_struct_0(sK80),sK81))) ),
    inference(subsumption_resolution,[],[f11479,f5692])).

fof(f11479,plain,
    ( r1_yellow_0(sK80,k3_waybel_0(sK80,k6_domain_1(u1_struct_0(sK80),sK81)))
    | v2_struct_0(sK80) ),
    inference(subsumption_resolution,[],[f11478,f5693])).

fof(f11478,plain,
    ( r1_yellow_0(sK80,k3_waybel_0(sK80,k6_domain_1(u1_struct_0(sK80),sK81)))
    | ~ v3_orders_2(sK80)
    | v2_struct_0(sK80) ),
    inference(subsumption_resolution,[],[f11477,f5694])).

fof(f11477,plain,
    ( r1_yellow_0(sK80,k3_waybel_0(sK80,k6_domain_1(u1_struct_0(sK80),sK81)))
    | ~ v4_orders_2(sK80)
    | ~ v3_orders_2(sK80)
    | v2_struct_0(sK80) ),
    inference(subsumption_resolution,[],[f11476,f5696])).

fof(f11476,plain,
    ( r1_yellow_0(sK80,k3_waybel_0(sK80,k6_domain_1(u1_struct_0(sK80),sK81)))
    | ~ l1_orders_2(sK80)
    | ~ v4_orders_2(sK80)
    | ~ v3_orders_2(sK80)
    | v2_struct_0(sK80) ),
    inference(subsumption_resolution,[],[f11351,f8331])).

fof(f11351,plain,
    ( ~ r1_yellow_0(sK80,k6_domain_1(u1_struct_0(sK80),sK81))
    | r1_yellow_0(sK80,k3_waybel_0(sK80,k6_domain_1(u1_struct_0(sK80),sK81)))
    | ~ l1_orders_2(sK80)
    | ~ v4_orders_2(sK80)
    | ~ v3_orders_2(sK80)
    | v2_struct_0(sK80) ),
    inference(resolution,[],[f8404,f5816])).

fof(f5816,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_yellow_0(X0,X1)
      | r1_yellow_0(X0,k3_waybel_0(X0,X1))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4721])).

fof(f4721,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_yellow_0(X0,X1)
              | ~ r1_yellow_0(X0,k3_waybel_0(X0,X1)) )
            & ( r1_yellow_0(X0,k3_waybel_0(X0,X1))
              | ~ r1_yellow_0(X0,X1) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3378])).

fof(f3378,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
          <=> r1_yellow_0(X0,k3_waybel_0(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3377])).

fof(f3377,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
          <=> r1_yellow_0(X0,k3_waybel_0(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3222])).

fof(f3222,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r1_yellow_0(X0,X1)
          <=> r1_yellow_0(X0,k3_waybel_0(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_waybel_0)).
%------------------------------------------------------------------------------
