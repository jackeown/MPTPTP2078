%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1659+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:29 EST 2020

% Result     : Theorem 4.56s
% Output     : Refutation 4.56s
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
fof(f10819,plain,(
    $false ),
    inference(subsumption_resolution,[],[f10818,f10812])).

fof(f10812,plain,(
    ~ r2_yellow_0(sK73,k6_waybel_0(sK73,sK74)) ),
    inference(trivial_inequality_removal,[],[f10811])).

fof(f10811,plain,
    ( sK74 != sK74
    | ~ r2_yellow_0(sK73,k6_waybel_0(sK73,sK74)) ),
    inference(backward_demodulation,[],[f5429,f10809])).

fof(f10809,plain,(
    sK74 = k2_yellow_0(sK73,k6_waybel_0(sK73,sK74)) ),
    inference(forward_demodulation,[],[f10808,f7787])).

fof(f7787,plain,(
    sK74 = k2_yellow_0(sK73,k6_domain_1(u1_struct_0(sK73),sK74)) ),
    inference(subsumption_resolution,[],[f7786,f5423])).

fof(f5423,plain,(
    ~ v2_struct_0(sK73) ),
    inference(cnf_transformation,[],[f4566])).

fof(f4566,plain,
    ( ( sK74 != k2_yellow_0(sK73,k6_waybel_0(sK73,sK74))
      | ~ r2_yellow_0(sK73,k6_waybel_0(sK73,sK74)) )
    & m1_subset_1(sK74,u1_struct_0(sK73))
    & l1_orders_2(sK73)
    & v5_orders_2(sK73)
    & v4_orders_2(sK73)
    & v3_orders_2(sK73)
    & ~ v2_struct_0(sK73) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK73,sK74])],[f3324,f4565,f4564])).

fof(f4564,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_yellow_0(X0,k6_waybel_0(X0,X1)) != X1
              | ~ r2_yellow_0(X0,k6_waybel_0(X0,X1)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( k2_yellow_0(sK73,k6_waybel_0(sK73,X1)) != X1
            | ~ r2_yellow_0(sK73,k6_waybel_0(sK73,X1)) )
          & m1_subset_1(X1,u1_struct_0(sK73)) )
      & l1_orders_2(sK73)
      & v5_orders_2(sK73)
      & v4_orders_2(sK73)
      & v3_orders_2(sK73)
      & ~ v2_struct_0(sK73) ) ),
    introduced(choice_axiom,[])).

fof(f4565,plain,
    ( ? [X1] :
        ( ( k2_yellow_0(sK73,k6_waybel_0(sK73,X1)) != X1
          | ~ r2_yellow_0(sK73,k6_waybel_0(sK73,X1)) )
        & m1_subset_1(X1,u1_struct_0(sK73)) )
   => ( ( sK74 != k2_yellow_0(sK73,k6_waybel_0(sK73,sK74))
        | ~ r2_yellow_0(sK73,k6_waybel_0(sK73,sK74)) )
      & m1_subset_1(sK74,u1_struct_0(sK73)) ) ),
    introduced(choice_axiom,[])).

fof(f3324,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_yellow_0(X0,k6_waybel_0(X0,X1)) != X1
            | ~ r2_yellow_0(X0,k6_waybel_0(X0,X1)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3323])).

fof(f3323,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_yellow_0(X0,k6_waybel_0(X0,X1)) != X1
            | ~ r2_yellow_0(X0,k6_waybel_0(X0,X1)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3235])).

fof(f3235,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( k2_yellow_0(X0,k6_waybel_0(X0,X1)) = X1
              & r2_yellow_0(X0,k6_waybel_0(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f3234])).

fof(f3234,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( k2_yellow_0(X0,k6_waybel_0(X0,X1)) = X1
            & r2_yellow_0(X0,k6_waybel_0(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_waybel_0)).

fof(f7786,plain,
    ( sK74 = k2_yellow_0(sK73,k6_domain_1(u1_struct_0(sK73),sK74))
    | v2_struct_0(sK73) ),
    inference(subsumption_resolution,[],[f7785,f5424])).

fof(f5424,plain,(
    v3_orders_2(sK73) ),
    inference(cnf_transformation,[],[f4566])).

fof(f7785,plain,
    ( sK74 = k2_yellow_0(sK73,k6_domain_1(u1_struct_0(sK73),sK74))
    | ~ v3_orders_2(sK73)
    | v2_struct_0(sK73) ),
    inference(subsumption_resolution,[],[f7784,f5426])).

fof(f5426,plain,(
    v5_orders_2(sK73) ),
    inference(cnf_transformation,[],[f4566])).

fof(f7784,plain,
    ( sK74 = k2_yellow_0(sK73,k6_domain_1(u1_struct_0(sK73),sK74))
    | ~ v5_orders_2(sK73)
    | ~ v3_orders_2(sK73)
    | v2_struct_0(sK73) ),
    inference(subsumption_resolution,[],[f7691,f5427])).

fof(f5427,plain,(
    l1_orders_2(sK73) ),
    inference(cnf_transformation,[],[f4566])).

fof(f7691,plain,
    ( sK74 = k2_yellow_0(sK73,k6_domain_1(u1_struct_0(sK73),sK74))
    | ~ l1_orders_2(sK73)
    | ~ v5_orders_2(sK73)
    | ~ v3_orders_2(sK73)
    | v2_struct_0(sK73) ),
    inference(resolution,[],[f5428,f5489])).

fof(f5489,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | k2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3365])).

fof(f3365,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
            & k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3364])).

fof(f3364,plain,(
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

fof(f5428,plain,(
    m1_subset_1(sK74,u1_struct_0(sK73)) ),
    inference(cnf_transformation,[],[f4566])).

fof(f10808,plain,(
    k2_yellow_0(sK73,k6_waybel_0(sK73,sK74)) = k2_yellow_0(sK73,k6_domain_1(u1_struct_0(sK73),sK74)) ),
    inference(forward_demodulation,[],[f10807,f7810])).

fof(f7810,plain,(
    k6_waybel_0(sK73,sK74) = k4_waybel_0(sK73,k6_domain_1(u1_struct_0(sK73),sK74)) ),
    inference(subsumption_resolution,[],[f7809,f5423])).

fof(f7809,plain,
    ( k6_waybel_0(sK73,sK74) = k4_waybel_0(sK73,k6_domain_1(u1_struct_0(sK73),sK74))
    | v2_struct_0(sK73) ),
    inference(subsumption_resolution,[],[f7699,f5427])).

fof(f7699,plain,
    ( k6_waybel_0(sK73,sK74) = k4_waybel_0(sK73,k6_domain_1(u1_struct_0(sK73),sK74))
    | ~ l1_orders_2(sK73)
    | v2_struct_0(sK73) ),
    inference(resolution,[],[f5428,f5582])).

fof(f5582,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | k6_waybel_0(X0,X1) = k4_waybel_0(X0,k6_domain_1(u1_struct_0(X0),X1))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3420])).

fof(f3420,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_waybel_0(X0,X1) = k4_waybel_0(X0,k6_domain_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3419])).

fof(f3419,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_waybel_0(X0,X1) = k4_waybel_0(X0,k6_domain_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3161])).

fof(f3161,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k6_waybel_0(X0,X1) = k4_waybel_0(X0,k6_domain_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_waybel_0)).

fof(f10807,plain,(
    k2_yellow_0(sK73,k6_domain_1(u1_struct_0(sK73),sK74)) = k2_yellow_0(sK73,k4_waybel_0(sK73,k6_domain_1(u1_struct_0(sK73),sK74))) ),
    inference(subsumption_resolution,[],[f10806,f5423])).

fof(f10806,plain,
    ( k2_yellow_0(sK73,k6_domain_1(u1_struct_0(sK73),sK74)) = k2_yellow_0(sK73,k4_waybel_0(sK73,k6_domain_1(u1_struct_0(sK73),sK74)))
    | v2_struct_0(sK73) ),
    inference(subsumption_resolution,[],[f10805,f5424])).

fof(f10805,plain,
    ( k2_yellow_0(sK73,k6_domain_1(u1_struct_0(sK73),sK74)) = k2_yellow_0(sK73,k4_waybel_0(sK73,k6_domain_1(u1_struct_0(sK73),sK74)))
    | ~ v3_orders_2(sK73)
    | v2_struct_0(sK73) ),
    inference(subsumption_resolution,[],[f10804,f5425])).

fof(f5425,plain,(
    v4_orders_2(sK73) ),
    inference(cnf_transformation,[],[f4566])).

fof(f10804,plain,
    ( k2_yellow_0(sK73,k6_domain_1(u1_struct_0(sK73),sK74)) = k2_yellow_0(sK73,k4_waybel_0(sK73,k6_domain_1(u1_struct_0(sK73),sK74)))
    | ~ v4_orders_2(sK73)
    | ~ v3_orders_2(sK73)
    | v2_struct_0(sK73) ),
    inference(subsumption_resolution,[],[f10803,f5427])).

fof(f10803,plain,
    ( k2_yellow_0(sK73,k6_domain_1(u1_struct_0(sK73),sK74)) = k2_yellow_0(sK73,k4_waybel_0(sK73,k6_domain_1(u1_struct_0(sK73),sK74)))
    | ~ l1_orders_2(sK73)
    | ~ v4_orders_2(sK73)
    | ~ v3_orders_2(sK73)
    | v2_struct_0(sK73) ),
    inference(subsumption_resolution,[],[f10733,f7797])).

fof(f7797,plain,(
    r2_yellow_0(sK73,k6_domain_1(u1_struct_0(sK73),sK74)) ),
    inference(subsumption_resolution,[],[f7796,f5423])).

fof(f7796,plain,
    ( r2_yellow_0(sK73,k6_domain_1(u1_struct_0(sK73),sK74))
    | v2_struct_0(sK73) ),
    inference(subsumption_resolution,[],[f7795,f5424])).

fof(f7795,plain,
    ( r2_yellow_0(sK73,k6_domain_1(u1_struct_0(sK73),sK74))
    | ~ v3_orders_2(sK73)
    | v2_struct_0(sK73) ),
    inference(subsumption_resolution,[],[f7794,f5426])).

fof(f7794,plain,
    ( r2_yellow_0(sK73,k6_domain_1(u1_struct_0(sK73),sK74))
    | ~ v5_orders_2(sK73)
    | ~ v3_orders_2(sK73)
    | v2_struct_0(sK73) ),
    inference(subsumption_resolution,[],[f7694,f5427])).

fof(f7694,plain,
    ( r2_yellow_0(sK73,k6_domain_1(u1_struct_0(sK73),sK74))
    | ~ l1_orders_2(sK73)
    | ~ v5_orders_2(sK73)
    | ~ v3_orders_2(sK73)
    | v2_struct_0(sK73) ),
    inference(resolution,[],[f5428,f5543])).

fof(f5543,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | r2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3396])).

fof(f3396,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1))
            & r1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3395])).

fof(f3395,plain,(
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

fof(f10733,plain,
    ( ~ r2_yellow_0(sK73,k6_domain_1(u1_struct_0(sK73),sK74))
    | k2_yellow_0(sK73,k6_domain_1(u1_struct_0(sK73),sK74)) = k2_yellow_0(sK73,k4_waybel_0(sK73,k6_domain_1(u1_struct_0(sK73),sK74)))
    | ~ l1_orders_2(sK73)
    | ~ v4_orders_2(sK73)
    | ~ v3_orders_2(sK73)
    | v2_struct_0(sK73) ),
    inference(resolution,[],[f7876,f5490])).

fof(f5490,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_yellow_0(X0,X1)
      | k2_yellow_0(X0,X1) = k2_yellow_0(X0,k4_waybel_0(X0,X1))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3367])).

fof(f3367,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_yellow_0(X0,X1) = k2_yellow_0(X0,k4_waybel_0(X0,X1))
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3366])).

fof(f3366,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_yellow_0(X0,X1) = k2_yellow_0(X0,k4_waybel_0(X0,X1))
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3233])).

fof(f3233,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_yellow_0(X0,X1)
           => k2_yellow_0(X0,X1) = k2_yellow_0(X0,k4_waybel_0(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_waybel_0)).

fof(f7876,plain,(
    m1_subset_1(k6_domain_1(u1_struct_0(sK73),sK74),k1_zfmisc_1(u1_struct_0(sK73))) ),
    inference(subsumption_resolution,[],[f7875,f5423])).

fof(f7875,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK73),sK74),k1_zfmisc_1(u1_struct_0(sK73)))
    | v2_struct_0(sK73) ),
    inference(subsumption_resolution,[],[f7874,f5424])).

fof(f7874,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK73),sK74),k1_zfmisc_1(u1_struct_0(sK73)))
    | ~ v3_orders_2(sK73)
    | v2_struct_0(sK73) ),
    inference(subsumption_resolution,[],[f7745,f5427])).

fof(f7745,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK73),sK74),k1_zfmisc_1(u1_struct_0(sK73)))
    | ~ l1_orders_2(sK73)
    | ~ v3_orders_2(sK73)
    | v2_struct_0(sK73) ),
    inference(resolution,[],[f5428,f6763])).

fof(f6763,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4090])).

fof(f4090,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f4089])).

fof(f4089,plain,(
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

fof(f5429,plain,
    ( sK74 != k2_yellow_0(sK73,k6_waybel_0(sK73,sK74))
    | ~ r2_yellow_0(sK73,k6_waybel_0(sK73,sK74)) ),
    inference(cnf_transformation,[],[f4566])).

fof(f10818,plain,(
    r2_yellow_0(sK73,k6_waybel_0(sK73,sK74)) ),
    inference(forward_demodulation,[],[f10817,f7810])).

fof(f10817,plain,(
    r2_yellow_0(sK73,k4_waybel_0(sK73,k6_domain_1(u1_struct_0(sK73),sK74))) ),
    inference(subsumption_resolution,[],[f10816,f5423])).

fof(f10816,plain,
    ( r2_yellow_0(sK73,k4_waybel_0(sK73,k6_domain_1(u1_struct_0(sK73),sK74)))
    | v2_struct_0(sK73) ),
    inference(subsumption_resolution,[],[f10815,f5424])).

fof(f10815,plain,
    ( r2_yellow_0(sK73,k4_waybel_0(sK73,k6_domain_1(u1_struct_0(sK73),sK74)))
    | ~ v3_orders_2(sK73)
    | v2_struct_0(sK73) ),
    inference(subsumption_resolution,[],[f10814,f5425])).

fof(f10814,plain,
    ( r2_yellow_0(sK73,k4_waybel_0(sK73,k6_domain_1(u1_struct_0(sK73),sK74)))
    | ~ v4_orders_2(sK73)
    | ~ v3_orders_2(sK73)
    | v2_struct_0(sK73) ),
    inference(subsumption_resolution,[],[f10813,f5427])).

fof(f10813,plain,
    ( r2_yellow_0(sK73,k4_waybel_0(sK73,k6_domain_1(u1_struct_0(sK73),sK74)))
    | ~ l1_orders_2(sK73)
    | ~ v4_orders_2(sK73)
    | ~ v3_orders_2(sK73)
    | v2_struct_0(sK73) ),
    inference(subsumption_resolution,[],[f10734,f7797])).

fof(f10734,plain,
    ( ~ r2_yellow_0(sK73,k6_domain_1(u1_struct_0(sK73),sK74))
    | r2_yellow_0(sK73,k4_waybel_0(sK73,k6_domain_1(u1_struct_0(sK73),sK74)))
    | ~ l1_orders_2(sK73)
    | ~ v4_orders_2(sK73)
    | ~ v3_orders_2(sK73)
    | v2_struct_0(sK73) ),
    inference(resolution,[],[f7876,f5544])).

fof(f5544,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_yellow_0(X0,X1)
      | r2_yellow_0(X0,k4_waybel_0(X0,X1))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4633])).

fof(f4633,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_yellow_0(X0,X1)
              | ~ r2_yellow_0(X0,k4_waybel_0(X0,X1)) )
            & ( r2_yellow_0(X0,k4_waybel_0(X0,X1))
              | ~ r2_yellow_0(X0,X1) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3398])).

fof(f3398,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
          <=> r2_yellow_0(X0,k4_waybel_0(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3397])).

fof(f3397,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
          <=> r2_yellow_0(X0,k4_waybel_0(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3232])).

fof(f3232,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_yellow_0(X0,X1)
          <=> r2_yellow_0(X0,k4_waybel_0(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_waybel_0)).
%------------------------------------------------------------------------------
