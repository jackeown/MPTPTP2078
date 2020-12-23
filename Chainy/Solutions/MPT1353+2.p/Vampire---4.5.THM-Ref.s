%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1353+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:19 EST 2020

% Result     : Theorem 2.59s
% Output     : Refutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 645 expanded)
%              Number of leaves         :   13 ( 178 expanded)
%              Depth                    :   20
%              Number of atoms          :  368 (3419 expanded)
%              Number of equality atoms :    8 (  16 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3853,plain,(
    $false ),
    inference(global_subsumption,[],[f2508,f3656,f3852])).

fof(f3852,plain,(
    ~ v1_tops_2(sK3,sK2) ),
    inference(subsumption_resolution,[],[f3836,f3680])).

fof(f3680,plain,(
    r2_hidden(sK5(sK3,u1_pre_topc(sK2)),sK3) ),
    inference(resolution,[],[f3656,f2519])).

fof(f2519,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f2482])).

fof(f2482,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f2480,f2481])).

fof(f2481,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f2480,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f2479])).

fof(f2479,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2445])).

fof(f2445,plain,(
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

fof(f3836,plain,
    ( ~ r2_hidden(sK5(sK3,u1_pre_topc(sK2)),sK3)
    | ~ v1_tops_2(sK3,sK2) ),
    inference(resolution,[],[f3696,f2659])).

fof(f2659,plain,
    ( ~ r2_hidden(sK5(sK3,u1_pre_topc(sK2)),u1_pre_topc(sK2))
    | ~ v1_tops_2(sK3,sK2) ),
    inference(resolution,[],[f2509,f2520])).

fof(f2520,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f2482])).

fof(f2509,plain,
    ( ~ r1_tarski(sK3,u1_pre_topc(sK2))
    | ~ v1_tops_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f2473])).

fof(f2473,plain,
    ( ( ~ r1_tarski(sK3,u1_pre_topc(sK2))
      | ~ v1_tops_2(sK3,sK2) )
    & ( r1_tarski(sK3,u1_pre_topc(sK2))
      | v1_tops_2(sK3,sK2) )
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    & l1_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f2470,f2472,f2471])).

fof(f2471,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_tarski(X1,u1_pre_topc(X0))
              | ~ v1_tops_2(X1,X0) )
            & ( r1_tarski(X1,u1_pre_topc(X0))
              | v1_tops_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ r1_tarski(X1,u1_pre_topc(sK2))
            | ~ v1_tops_2(X1,sK2) )
          & ( r1_tarski(X1,u1_pre_topc(sK2))
            | v1_tops_2(X1,sK2) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) )
      & l1_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f2472,plain,
    ( ? [X1] :
        ( ( ~ r1_tarski(X1,u1_pre_topc(sK2))
          | ~ v1_tops_2(X1,sK2) )
        & ( r1_tarski(X1,u1_pre_topc(sK2))
          | v1_tops_2(X1,sK2) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) )
   => ( ( ~ r1_tarski(sK3,u1_pre_topc(sK2))
        | ~ v1_tops_2(sK3,sK2) )
      & ( r1_tarski(sK3,u1_pre_topc(sK2))
        | v1_tops_2(sK3,sK2) )
      & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ) ),
    introduced(choice_axiom,[])).

fof(f2470,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,u1_pre_topc(X0))
            | ~ v1_tops_2(X1,X0) )
          & ( r1_tarski(X1,u1_pre_topc(X0))
            | v1_tops_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2469])).

fof(f2469,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,u1_pre_topc(X0))
            | ~ v1_tops_2(X1,X0) )
          & ( r1_tarski(X1,u1_pre_topc(X0))
            | v1_tops_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f2441])).

fof(f2441,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tops_2(X1,X0)
          <~> r1_tarski(X1,u1_pre_topc(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2433])).

fof(f2433,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ( v1_tops_2(X1,X0)
            <=> r1_tarski(X1,u1_pre_topc(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f2432])).

fof(f2432,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_tops_2)).

fof(f3696,plain,(
    ! [X0] :
      ( r2_hidden(X0,u1_pre_topc(sK2))
      | ~ r2_hidden(X0,sK3) ) ),
    inference(subsumption_resolution,[],[f3695,f2966])).

fof(f2966,plain,(
    ! [X5] :
      ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r2_hidden(X5,sK3) ) ),
    inference(resolution,[],[f2947,f2513])).

fof(f2513,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2474])).

fof(f2474,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f609])).

fof(f609,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f2947,plain,(
    ! [X0] :
      ( r1_tarski(X0,u1_struct_0(sK2))
      | ~ r2_hidden(X0,sK3) ) ),
    inference(resolution,[],[f2650,f2558])).

fof(f2558,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f2514])).

fof(f2514,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2478])).

fof(f2478,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK4(X0,X1),X0)
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( r1_tarski(sK4(X0,X1),X0)
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f2476,f2477])).

fof(f2477,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK4(X0,X1),X0)
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( r1_tarski(sK4(X0,X1),X0)
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f2476,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f2475])).

fof(f2475,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f285])).

fof(f285,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f2650,plain,(
    ! [X2] :
      ( r2_hidden(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r2_hidden(X2,sK3) ) ),
    inference(resolution,[],[f2600,f2518])).

fof(f2518,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2482])).

fof(f2600,plain,(
    r1_tarski(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(resolution,[],[f2507,f2512])).

fof(f2512,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f2474])).

fof(f2507,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f2473])).

fof(f3695,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | r2_hidden(X0,u1_pre_topc(sK2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(subsumption_resolution,[],[f3694,f2506])).

fof(f2506,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f2473])).

fof(f3694,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | r2_hidden(X0,u1_pre_topc(sK2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_pre_topc(sK2) ) ),
    inference(subsumption_resolution,[],[f3690,f3656])).

fof(f3690,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | r1_tarski(sK3,u1_pre_topc(sK2))
      | r2_hidden(X0,u1_pre_topc(sK2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_pre_topc(sK2) ) ),
    inference(resolution,[],[f2996,f2530])).

fof(f2530,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2489])).

fof(f2489,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f2451])).

fof(f2451,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1774])).

fof(f1774,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f2996,plain,(
    ! [X0] :
      ( v3_pre_topc(X0,sK2)
      | ~ r2_hidden(X0,sK3)
      | r1_tarski(sK3,u1_pre_topc(sK2)) ) ),
    inference(subsumption_resolution,[],[f2988,f2947])).

fof(f2988,plain,(
    ! [X0] :
      ( v3_pre_topc(X0,sK2)
      | ~ r2_hidden(X0,sK3)
      | r1_tarski(sK3,u1_pre_topc(sK2))
      | ~ r1_tarski(X0,u1_struct_0(sK2)) ) ),
    inference(resolution,[],[f2643,f2513])).

fof(f2643,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK2)))
      | v3_pre_topc(X5,sK2)
      | ~ r2_hidden(X5,sK3)
      | r1_tarski(sK3,u1_pre_topc(sK2)) ) ),
    inference(subsumption_resolution,[],[f2642,f2506])).

fof(f2642,plain,(
    ! [X5] :
      ( r1_tarski(sK3,u1_pre_topc(sK2))
      | v3_pre_topc(X5,sK2)
      | ~ r2_hidden(X5,sK3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_pre_topc(sK2) ) ),
    inference(subsumption_resolution,[],[f2630,f2507])).

fof(f2630,plain,(
    ! [X5] :
      ( r1_tarski(sK3,u1_pre_topc(sK2))
      | v3_pre_topc(X5,sK2)
      | ~ r2_hidden(X5,sK3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
      | ~ l1_pre_topc(sK2) ) ),
    inference(resolution,[],[f2508,f2551])).

fof(f2551,plain,(
    ! [X0,X3,X1] :
      ( v3_pre_topc(X3,X0)
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2501])).

fof(f2501,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ( ~ v3_pre_topc(sK11(X0,X1),X0)
                & r2_hidden(sK11(X0,X1),X1)
                & m1_subset_1(sK11(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f2499,f2500])).

fof(f2500,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_pre_topc(X2,X0)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK11(X0,X1),X0)
        & r2_hidden(sK11(X0,X1),X1)
        & m1_subset_1(sK11(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f2499,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f2498])).

fof(f2498,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v3_pre_topc(X2,X0)
                  | ~ r2_hidden(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f2465])).

fof(f2465,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2464])).

fof(f2464,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2242])).

fof(f2242,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_2)).

fof(f3656,plain,(
    ~ r1_tarski(sK3,u1_pre_topc(sK2)) ),
    inference(resolution,[],[f3655,f2962])).

fof(f2962,plain,
    ( ~ v1_tops_2(u1_pre_topc(sK2),sK2)
    | ~ r1_tarski(sK3,u1_pre_topc(sK2)) ),
    inference(subsumption_resolution,[],[f2961,f2509])).

fof(f2961,plain,
    ( ~ v1_tops_2(u1_pre_topc(sK2),sK2)
    | ~ r1_tarski(sK3,u1_pre_topc(sK2))
    | v1_tops_2(sK3,sK2) ),
    inference(subsumption_resolution,[],[f2955,f2506])).

fof(f2955,plain,
    ( ~ v1_tops_2(u1_pre_topc(sK2),sK2)
    | ~ r1_tarski(sK3,u1_pre_topc(sK2))
    | v1_tops_2(sK3,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f2611,f2545])).

fof(f2545,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2453])).

fof(f2453,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1786])).

fof(f1786,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f2611,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
      | ~ v1_tops_2(X0,sK2)
      | ~ r1_tarski(sK3,X0)
      | v1_tops_2(sK3,sK2) ) ),
    inference(subsumption_resolution,[],[f2586,f2506])).

fof(f2586,plain,(
    ! [X0] :
      ( v1_tops_2(sK3,sK2)
      | ~ v1_tops_2(X0,sK2)
      | ~ r1_tarski(sK3,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
      | ~ l1_pre_topc(sK2) ) ),
    inference(resolution,[],[f2507,f2546])).

fof(f2546,plain,(
    ! [X2,X0,X1] :
      ( v1_tops_2(X1,X0)
      | ~ v1_tops_2(X2,X0)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2455])).

fof(f2455,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_2(X1,X0)
              | ~ v1_tops_2(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2454])).

fof(f2454,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_2(X1,X0)
              | ~ v1_tops_2(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2367])).

fof(f2367,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( ( v1_tops_2(X2,X0)
                  & r1_tarski(X1,X2) )
               => v1_tops_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_tops_2)).

fof(f3655,plain,(
    v1_tops_2(u1_pre_topc(sK2),sK2) ),
    inference(subsumption_resolution,[],[f3654,f2700])).

fof(f2700,plain,
    ( v1_tops_2(u1_pre_topc(sK2),sK2)
    | m1_subset_1(sK11(sK2,u1_pre_topc(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subsumption_resolution,[],[f2676,f2506])).

fof(f2676,plain,
    ( v1_tops_2(u1_pre_topc(sK2),sK2)
    | m1_subset_1(sK11(sK2,u1_pre_topc(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f2575,f2552])).

fof(f2552,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | m1_subset_1(sK11(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2501])).

fof(f2575,plain,(
    m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(resolution,[],[f2506,f2545])).

fof(f3654,plain,
    ( v1_tops_2(u1_pre_topc(sK2),sK2)
    | ~ m1_subset_1(sK11(sK2,u1_pre_topc(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subsumption_resolution,[],[f3653,f2701])).

fof(f2701,plain,
    ( v1_tops_2(u1_pre_topc(sK2),sK2)
    | r2_hidden(sK11(sK2,u1_pre_topc(sK2)),u1_pre_topc(sK2)) ),
    inference(subsumption_resolution,[],[f2677,f2506])).

fof(f2677,plain,
    ( v1_tops_2(u1_pre_topc(sK2),sK2)
    | r2_hidden(sK11(sK2,u1_pre_topc(sK2)),u1_pre_topc(sK2))
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f2575,f2553])).

fof(f2553,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | r2_hidden(sK11(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2501])).

fof(f3653,plain,
    ( v1_tops_2(u1_pre_topc(sK2),sK2)
    | ~ r2_hidden(sK11(sK2,u1_pre_topc(sK2)),u1_pre_topc(sK2))
    | ~ m1_subset_1(sK11(sK2,u1_pre_topc(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subsumption_resolution,[],[f3650,f2506])).

fof(f3650,plain,
    ( v1_tops_2(u1_pre_topc(sK2),sK2)
    | ~ r2_hidden(sK11(sK2,u1_pre_topc(sK2)),u1_pre_topc(sK2))
    | ~ m1_subset_1(sK11(sK2,u1_pre_topc(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f2702,f2531])).

fof(f2531,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2489])).

fof(f2702,plain,
    ( ~ v3_pre_topc(sK11(sK2,u1_pre_topc(sK2)),sK2)
    | v1_tops_2(u1_pre_topc(sK2),sK2) ),
    inference(subsumption_resolution,[],[f2678,f2506])).

fof(f2678,plain,
    ( v1_tops_2(u1_pre_topc(sK2),sK2)
    | ~ v3_pre_topc(sK11(sK2,u1_pre_topc(sK2)),sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f2575,f2554])).

fof(f2554,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | ~ v3_pre_topc(sK11(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2501])).

fof(f2508,plain,
    ( v1_tops_2(sK3,sK2)
    | r1_tarski(sK3,u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f2473])).
%------------------------------------------------------------------------------
