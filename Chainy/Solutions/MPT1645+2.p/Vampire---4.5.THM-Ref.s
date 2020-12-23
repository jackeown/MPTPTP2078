%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1645+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:28 EST 2020

% Result     : Theorem 2.08s
% Output     : Refutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 346 expanded)
%              Number of leaves         :    8 ( 156 expanded)
%              Depth                    :    9
%              Number of atoms          :  256 (3637 expanded)
%              Number of equality atoms :   48 ( 706 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4372,plain,(
    $false ),
    inference(global_subsumption,[],[f3550,f3984,f3985,f3986,f4345,f4350,f4366,f4369])).

fof(f4369,plain,
    ( ~ r1_tarski(k3_waybel_0(sK0,sK3),sK3)
    | v12_waybel_0(sK3,sK1) ),
    inference(backward_demodulation,[],[f4318,f4354])).

fof(f4354,plain,(
    k3_waybel_0(sK1,sK3) = k3_waybel_0(sK0,sK3) ),
    inference(unit_resulting_resolution,[],[f3542,f3541,f3987,f3545,f3543,f3997])).

fof(f3997,plain,(
    ! [X0,X3,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | k3_waybel_0(X1,X3) = k3_waybel_0(X0,X3)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f3640])).

fof(f3640,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_waybel_0(X0,X2) = k3_waybel_0(X1,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3285])).

fof(f3285,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k4_waybel_0(X0,X2) = k4_waybel_0(X1,X3)
                    & k3_waybel_0(X0,X2) = k3_waybel_0(X1,X3) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f3284])).

fof(f3284,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k4_waybel_0(X0,X2) = k4_waybel_0(X1,X3)
                    & k3_waybel_0(X0,X2) = k3_waybel_0(X1,X3) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3196])).

fof(f3196,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( X2 = X3
                     => ( k4_waybel_0(X0,X2) = k4_waybel_0(X1,X3)
                        & k3_waybel_0(X0,X2) = k3_waybel_0(X1,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_waybel_0)).

fof(f3543,plain,(
    g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) ),
    inference(cnf_transformation,[],[f3363])).

fof(f3363,plain,
    ( ( ( ~ v13_waybel_0(sK3,sK1)
        & v13_waybel_0(sK2,sK0) )
      | ( ~ v12_waybel_0(sK3,sK1)
        & v12_waybel_0(sK2,sK0) ) )
    & sK2 = sK3
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
    & l1_orders_2(sK1)
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f3228,f3362,f3361,f3360,f3359])).

fof(f3359,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ( ~ v13_waybel_0(X3,X1)
                        & v13_waybel_0(X2,X0) )
                      | ( ~ v12_waybel_0(X3,X1)
                        & v12_waybel_0(X2,X0) ) )
                    & X2 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
            & l1_orders_2(X1) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ v13_waybel_0(X3,X1)
                      & v13_waybel_0(X2,sK0) )
                    | ( ~ v12_waybel_0(X3,X1)
                      & v12_waybel_0(X2,sK0) ) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
          & l1_orders_2(X1) )
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f3360,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ( ~ v13_waybel_0(X3,X1)
                    & v13_waybel_0(X2,sK0) )
                  | ( ~ v12_waybel_0(X3,X1)
                    & v12_waybel_0(X2,sK0) ) )
                & X2 = X3
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        & l1_orders_2(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ( ~ v13_waybel_0(X3,sK1)
                  & v13_waybel_0(X2,sK0) )
                | ( ~ v12_waybel_0(X3,sK1)
                  & v12_waybel_0(X2,sK0) ) )
              & X2 = X3
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
      & l1_orders_2(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f3361,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ( ~ v13_waybel_0(X3,sK1)
                & v13_waybel_0(X2,sK0) )
              | ( ~ v12_waybel_0(X3,sK1)
                & v12_waybel_0(X2,sK0) ) )
            & X2 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X3] :
          ( ( ( ~ v13_waybel_0(X3,sK1)
              & v13_waybel_0(sK2,sK0) )
            | ( ~ v12_waybel_0(X3,sK1)
              & v12_waybel_0(sK2,sK0) ) )
          & sK2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f3362,plain,
    ( ? [X3] :
        ( ( ( ~ v13_waybel_0(X3,sK1)
            & v13_waybel_0(sK2,sK0) )
          | ( ~ v12_waybel_0(X3,sK1)
            & v12_waybel_0(sK2,sK0) ) )
        & sK2 = X3
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
   => ( ( ( ~ v13_waybel_0(sK3,sK1)
          & v13_waybel_0(sK2,sK0) )
        | ( ~ v12_waybel_0(sK3,sK1)
          & v12_waybel_0(sK2,sK0) ) )
      & sK2 = sK3
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f3228,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ v13_waybel_0(X3,X1)
                      & v13_waybel_0(X2,X0) )
                    | ( ~ v12_waybel_0(X3,X1)
                      & v12_waybel_0(X2,X0) ) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f3227])).

fof(f3227,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ v13_waybel_0(X3,X1)
                      & v13_waybel_0(X2,X0) )
                    | ( ~ v12_waybel_0(X3,X1)
                      & v12_waybel_0(X2,X0) ) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3210])).

fof(f3210,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( l1_orders_2(X1)
           => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( X2 = X3
                       => ( ( v13_waybel_0(X2,X0)
                           => v13_waybel_0(X3,X1) )
                          & ( v12_waybel_0(X2,X0)
                           => v12_waybel_0(X3,X1) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3209])).

fof(f3209,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( X2 = X3
                     => ( ( v13_waybel_0(X2,X0)
                         => v13_waybel_0(X3,X1) )
                        & ( v12_waybel_0(X2,X0)
                         => v12_waybel_0(X3,X1) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_waybel_0)).

fof(f3545,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f3363])).

fof(f3987,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(definition_unfolding,[],[f3544,f3546])).

fof(f3546,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f3363])).

fof(f3544,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f3363])).

fof(f3541,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f3363])).

fof(f3542,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f3363])).

fof(f4318,plain,
    ( ~ r1_tarski(k3_waybel_0(sK1,sK3),sK3)
    | v12_waybel_0(sK3,sK1) ),
    inference(subsumption_resolution,[],[f4300,f3542])).

fof(f4300,plain,
    ( ~ r1_tarski(k3_waybel_0(sK1,sK3),sK3)
    | v12_waybel_0(sK3,sK1)
    | ~ l1_orders_2(sK1) ),
    inference(resolution,[],[f3545,f3569])).

fof(f3569,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(k3_waybel_0(X0,X1),X1)
      | v12_waybel_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3377])).

fof(f3377,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v12_waybel_0(X1,X0)
              | ~ r1_tarski(k3_waybel_0(X0,X1),X1) )
            & ( r1_tarski(k3_waybel_0(X0,X1),X1)
              | ~ v12_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f3235])).

fof(f3235,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v12_waybel_0(X1,X0)
          <=> r1_tarski(k3_waybel_0(X0,X1),X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3207])).

fof(f3207,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v12_waybel_0(X1,X0)
          <=> r1_tarski(k3_waybel_0(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_waybel_0)).

fof(f4366,plain,
    ( ~ r1_tarski(k4_waybel_0(sK0,sK3),sK3)
    | v13_waybel_0(sK3,sK1) ),
    inference(backward_demodulation,[],[f4313,f4355])).

fof(f4355,plain,(
    k4_waybel_0(sK1,sK3) = k4_waybel_0(sK0,sK3) ),
    inference(unit_resulting_resolution,[],[f3542,f3541,f3987,f3545,f3543,f3996])).

fof(f3996,plain,(
    ! [X0,X3,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | k4_waybel_0(X1,X3) = k4_waybel_0(X0,X3)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f3641])).

fof(f3641,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_waybel_0(X0,X2) = k4_waybel_0(X1,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3285])).

fof(f4313,plain,
    ( ~ r1_tarski(k4_waybel_0(sK1,sK3),sK3)
    | v13_waybel_0(sK3,sK1) ),
    inference(subsumption_resolution,[],[f4295,f3542])).

fof(f4295,plain,
    ( ~ r1_tarski(k4_waybel_0(sK1,sK3),sK3)
    | v13_waybel_0(sK3,sK1)
    | ~ l1_orders_2(sK1) ),
    inference(resolution,[],[f3545,f3561])).

fof(f3561,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(k4_waybel_0(X0,X1),X1)
      | v13_waybel_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3371])).

fof(f3371,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ~ r1_tarski(k4_waybel_0(X0,X1),X1) )
            & ( r1_tarski(k4_waybel_0(X0,X1),X1)
              | ~ v13_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f3232])).

fof(f3232,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> r1_tarski(k4_waybel_0(X0,X1),X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3208])).

fof(f3208,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v13_waybel_0(X1,X0)
          <=> r1_tarski(k4_waybel_0(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_waybel_0)).

fof(f4350,plain,
    ( ~ v12_waybel_0(sK3,sK0)
    | r1_tarski(k3_waybel_0(sK0,sK3),sK3) ),
    inference(subsumption_resolution,[],[f4332,f3541])).

fof(f4332,plain,
    ( ~ v12_waybel_0(sK3,sK0)
    | r1_tarski(k3_waybel_0(sK0,sK3),sK3)
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f3987,f3568])).

fof(f3568,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | r1_tarski(k3_waybel_0(X0,X1),X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3377])).

fof(f4345,plain,
    ( ~ v13_waybel_0(sK3,sK0)
    | r1_tarski(k4_waybel_0(sK0,sK3),sK3) ),
    inference(subsumption_resolution,[],[f4327,f3541])).

fof(f4327,plain,
    ( ~ v13_waybel_0(sK3,sK0)
    | r1_tarski(k4_waybel_0(sK0,sK3),sK3)
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f3987,f3560])).

fof(f3560,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | r1_tarski(k4_waybel_0(X0,X1),X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3371])).

fof(f3986,plain,
    ( v13_waybel_0(sK3,sK0)
    | v12_waybel_0(sK3,sK0) ),
    inference(definition_unfolding,[],[f3547,f3546,f3546])).

fof(f3547,plain,
    ( v13_waybel_0(sK2,sK0)
    | v12_waybel_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f3363])).

fof(f3985,plain,
    ( v13_waybel_0(sK3,sK0)
    | ~ v12_waybel_0(sK3,sK1) ),
    inference(definition_unfolding,[],[f3548,f3546])).

fof(f3548,plain,
    ( v13_waybel_0(sK2,sK0)
    | ~ v12_waybel_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f3363])).

fof(f3984,plain,
    ( ~ v13_waybel_0(sK3,sK1)
    | v12_waybel_0(sK3,sK0) ),
    inference(definition_unfolding,[],[f3549,f3546])).

fof(f3549,plain,
    ( ~ v13_waybel_0(sK3,sK1)
    | v12_waybel_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f3363])).

fof(f3550,plain,
    ( ~ v13_waybel_0(sK3,sK1)
    | ~ v12_waybel_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f3363])).
%------------------------------------------------------------------------------
