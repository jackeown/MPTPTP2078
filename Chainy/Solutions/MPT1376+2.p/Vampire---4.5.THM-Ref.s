%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1376+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:19 EST 2020

% Result     : Theorem 5.34s
% Output     : Refutation 5.34s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 710 expanded)
%              Number of leaves         :    8 ( 179 expanded)
%              Depth                    :   21
%              Number of atoms          :  284 (4358 expanded)
%              Number of equality atoms :   27 ( 180 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5947,plain,(
    $false ),
    inference(subsumption_resolution,[],[f5946,f3904])).

fof(f3904,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(duplicate_literal_removal,[],[f3846])).

fof(f3846,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(backward_demodulation,[],[f2631,f3844])).

fof(f3844,plain,(
    u1_struct_0(sK2) = u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(subsumption_resolution,[],[f3843,f2627])).

fof(f2627,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f2584])).

fof(f2584,plain,
    ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))
      | ~ v1_tops_2(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
      | ~ v1_tops_2(sK3,sK2) )
    & ( ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))
        & v1_tops_2(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) )
      | ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
        & v1_tops_2(sK3,sK2) ) )
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f2581,f2583,f2582])).

fof(f2582,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
              | ~ v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
              | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              | ~ v1_tops_2(X1,X0) )
            & ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
                & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
              | ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
                & v1_tops_2(X1,X0) ) ) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))
            | ~ v1_tops_2(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
            | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
            | ~ v1_tops_2(X1,sK2) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))
              & v1_tops_2(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) )
            | ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
              & v1_tops_2(X1,sK2) ) ) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f2583,plain,
    ( ? [X1] :
        ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))
          | ~ v1_tops_2(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
          | ~ v1_tops_2(X1,sK2) )
        & ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))
            & v1_tops_2(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) )
          | ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
            & v1_tops_2(X1,sK2) ) ) )
   => ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))
        | ~ v1_tops_2(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
        | ~ v1_tops_2(sK3,sK2) )
      & ( ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))
          & v1_tops_2(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) )
        | ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
          & v1_tops_2(sK3,sK2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f2581,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
            | ~ v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
            | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            | ~ v1_tops_2(X1,X0) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
              & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              & v1_tops_2(X1,X0) ) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f2580])).

fof(f2580,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
            | ~ v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
            | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            | ~ v1_tops_2(X1,X0) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
              & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              & v1_tops_2(X1,X0) ) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f2524])).

fof(f2524,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            & v1_tops_2(X1,X0) )
        <~> ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
            & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f2523])).

fof(f2523,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            & v1_tops_2(X1,X0) )
        <~> ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
            & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2511])).

fof(f2511,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              & v1_tops_2(X1,X0) )
          <=> ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
              & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f2510])).

fof(f2510,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            & v1_tops_2(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
            & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_compts_1)).

fof(f3843,plain,
    ( u1_struct_0(sK2) = u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f3725,f2698])).

fof(f2698,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2557])).

fof(f2557,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1786])).

fof(f1786,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f3725,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | u1_struct_0(sK2) = u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(equality_resolution,[],[f2910])).

fof(f2910,plain,(
    ! [X10,X9] :
      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(X9,X10)
      | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = X9
      | ~ m1_subset_1(X10,k1_zfmisc_1(k1_zfmisc_1(X9))) ) ),
    inference(superposition,[],[f2635,f2881])).

fof(f2881,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) ),
    inference(resolution,[],[f2737,f2627])).

fof(f2737,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(X1)
      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) ) ),
    inference(subsumption_resolution,[],[f2733,f2726])).

fof(f2726,plain,(
    ! [X0] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f2698,f2638])).

fof(f2638,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f2528])).

fof(f2528,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f1777])).

fof(f1777,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(f2733,plain,(
    ! [X1] :
      ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f2657,f2727])).

fof(f2727,plain,(
    ! [X1] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f2698,f2637])).

fof(f2637,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | v1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f2528])).

fof(f2657,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2546])).

fof(f2546,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2545])).

fof(f2545,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1759])).

fof(f1759,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f2635,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f2527])).

fof(f2527,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f1808])).

fof(f1808,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(f2631,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))
    | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f2584])).

fof(f5946,plain,(
    ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(subsumption_resolution,[],[f5941,f3760])).

fof(f3760,plain,(
    r1_tarski(sK3,u1_pre_topc(sK2)) ),
    inference(subsumption_resolution,[],[f3759,f3730])).

fof(f3730,plain,
    ( r1_tarski(sK3,u1_pre_topc(sK2))
    | v1_tops_2(sK3,sK2) ),
    inference(backward_demodulation,[],[f2799,f3727])).

fof(f3727,plain,(
    u1_pre_topc(sK2) = u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(subsumption_resolution,[],[f3726,f2627])).

fof(f3726,plain,
    ( u1_pre_topc(sK2) = u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f3721,f2698])).

fof(f3721,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | u1_pre_topc(sK2) = u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(equality_resolution,[],[f2908])).

fof(f2908,plain,(
    ! [X6,X5] :
      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(X5,X6)
      | u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = X6
      | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(X5))) ) ),
    inference(superposition,[],[f2636,f2881])).

fof(f2636,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X1 = X3
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f2527])).

fof(f2799,plain,
    ( r1_tarski(sK3,u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | v1_tops_2(sK3,sK2) ),
    inference(subsumption_resolution,[],[f2798,f2627])).

fof(f2798,plain,
    ( r1_tarski(sK3,u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | v1_tops_2(sK3,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f2763,f2726])).

fof(f2763,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | r1_tarski(sK3,u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | v1_tops_2(sK3,sK2) ),
    inference(subsumption_resolution,[],[f2758,f2628])).

fof(f2628,plain,
    ( v1_tops_2(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | v1_tops_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f2584])).

fof(f2758,plain,
    ( ~ v1_tops_2(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | r1_tarski(sK3,u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | v1_tops_2(sK3,sK2) ),
    inference(resolution,[],[f2713,f2630])).

fof(f2630,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))
    | v1_tops_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f2584])).

fof(f2713,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v1_tops_2(X1,X0)
      | r1_tarski(X1,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2622])).

fof(f2622,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ~ r1_tarski(X1,u1_pre_topc(X0)) )
            & ( r1_tarski(X1,u1_pre_topc(X0))
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f2574])).

fof(f2574,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2432])).

fof(f2432,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tops_2)).

fof(f3759,plain,
    ( r1_tarski(sK3,u1_pre_topc(sK2))
    | ~ v1_tops_2(sK3,sK2) ),
    inference(subsumption_resolution,[],[f3758,f2627])).

fof(f3758,plain,
    ( r1_tarski(sK3,u1_pre_topc(sK2))
    | ~ v1_tops_2(sK3,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(duplicate_literal_removal,[],[f3754])).

fof(f3754,plain,
    ( r1_tarski(sK3,u1_pre_topc(sK2))
    | ~ v1_tops_2(sK3,sK2)
    | r1_tarski(sK3,u1_pre_topc(sK2))
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f3734,f2713])).

fof(f3734,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | r1_tarski(sK3,u1_pre_topc(sK2)) ),
    inference(backward_demodulation,[],[f2872,f3727])).

fof(f2872,plain,
    ( r1_tarski(sK3,u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(subsumption_resolution,[],[f2871,f2627])).

fof(f2871,plain,
    ( r1_tarski(sK3,u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f2771,f2726])).

fof(f2771,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | r1_tarski(sK3,u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(subsumption_resolution,[],[f2767,f2629])).

fof(f2629,plain,
    ( v1_tops_2(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f2584])).

fof(f2767,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ v1_tops_2(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | r1_tarski(sK3,u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(resolution,[],[f2631,f2713])).

fof(f5941,plain,
    ( ~ r1_tarski(sK3,u1_pre_topc(sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(resolution,[],[f5940,f3908])).

fof(f3908,plain,(
    ~ v1_tops_2(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(subsumption_resolution,[],[f3907,f3905])).

fof(f3905,plain,(
    v1_tops_2(sK3,sK2) ),
    inference(subsumption_resolution,[],[f3845,f3751])).

fof(f3751,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | v1_tops_2(sK3,sK2) ),
    inference(subsumption_resolution,[],[f3750,f2627])).

fof(f3750,plain,
    ( v1_tops_2(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ l1_pre_topc(sK2) ),
    inference(duplicate_literal_removal,[],[f3749])).

fof(f3749,plain,
    ( v1_tops_2(sK3,sK2)
    | v1_tops_2(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f3730,f2714])).

fof(f2714,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,u1_pre_topc(X0))
      | v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2622])).

fof(f3845,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | v1_tops_2(sK3,sK2) ),
    inference(backward_demodulation,[],[f2630,f3844])).

fof(f3907,plain,
    ( ~ v1_tops_2(sK3,sK2)
    | ~ v1_tops_2(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(subsumption_resolution,[],[f3903,f3904])).

fof(f3903,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ v1_tops_2(sK3,sK2)
    | ~ v1_tops_2(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(duplicate_literal_removal,[],[f3847])).

fof(f3847,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ v1_tops_2(sK3,sK2)
    | ~ v1_tops_2(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(backward_demodulation,[],[f2632,f3844])).

fof(f2632,plain,
    ( ~ v1_tops_2(sK3,sK2)
    | ~ v1_tops_2(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) ),
    inference(cnf_transformation,[],[f2584])).

fof(f5940,plain,(
    ! [X0] :
      ( v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
      | ~ r1_tarski(X0,u1_pre_topc(sK2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ) ),
    inference(subsumption_resolution,[],[f5939,f2627])).

fof(f5939,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,u1_pre_topc(sK2))
      | v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
      | ~ l1_pre_topc(sK2) ) ),
    inference(resolution,[],[f3898,f2726])).

fof(f3898,plain,(
    ! [X8] :
      ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
      | ~ r1_tarski(X8,u1_pre_topc(sK2))
      | v1_tops_2(X8,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
      | ~ m1_subset_1(X8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ) ),
    inference(backward_demodulation,[],[f3782,f3844])).

fof(f3782,plain,(
    ! [X8] :
      ( ~ r1_tarski(X8,u1_pre_topc(sK2))
      | v1_tops_2(X8,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
      | ~ m1_subset_1(X8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ) ),
    inference(superposition,[],[f2714,f3727])).
%------------------------------------------------------------------------------
