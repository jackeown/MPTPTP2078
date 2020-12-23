%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1790+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:32 EST 2020

% Result     : Theorem 1.90s
% Output     : Refutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 179 expanded)
%              Number of leaves         :    8 (  68 expanded)
%              Depth                    :   12
%              Number of atoms          :  197 (1151 expanded)
%              Number of equality atoms :   23 ( 189 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4962,plain,(
    $false ),
    inference(subsumption_resolution,[],[f4961,f4751])).

fof(f4751,plain,(
    r2_hidden(sK3,k5_tmap_1(sK2,sK3)) ),
    inference(subsumption_resolution,[],[f4750,f3807])).

fof(f3807,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f3680])).

fof(f3680,plain,
    ( ~ v3_pre_topc(sK4,k6_tmap_1(sK2,sK3))
    & sK3 = sK4
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK2,sK3))))
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f3480,f3679,f3678,f3677])).

fof(f3677,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v3_pre_topc(X2,k6_tmap_1(X0,X1))
                & X1 = X2
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_pre_topc(X2,k6_tmap_1(sK2,X1))
              & X1 = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK2,X1)))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f3678,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v3_pre_topc(X2,k6_tmap_1(sK2,X1))
            & X1 = X2
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK2,X1)))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
   => ( ? [X2] :
          ( ~ v3_pre_topc(X2,k6_tmap_1(sK2,sK3))
          & sK3 = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK2,sK3)))) )
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f3679,plain,
    ( ? [X2] :
        ( ~ v3_pre_topc(X2,k6_tmap_1(sK2,sK3))
        & sK3 = X2
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK2,sK3)))) )
   => ( ~ v3_pre_topc(sK4,k6_tmap_1(sK2,sK3))
      & sK3 = sK4
      & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK2,sK3)))) ) ),
    introduced(choice_axiom,[])).

fof(f3480,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_pre_topc(X2,k6_tmap_1(X0,X1))
              & X1 = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3479])).

fof(f3479,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_pre_topc(X2,k6_tmap_1(X0,X1))
              & X1 = X2
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3368])).

fof(f3368,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))
               => ( X1 = X2
                 => v3_pre_topc(X2,k6_tmap_1(X0,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f3367])).

fof(f3367,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))
             => ( X1 = X2
               => v3_pre_topc(X2,k6_tmap_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_tmap_1)).

fof(f4750,plain,
    ( r2_hidden(sK3,k5_tmap_1(sK2,sK3))
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f4749,f3808])).

fof(f3808,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f3680])).

fof(f4749,plain,
    ( r2_hidden(sK3,k5_tmap_1(sK2,sK3))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f4520,f3809])).

fof(f3809,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f3680])).

fof(f4520,plain,
    ( r2_hidden(sK3,k5_tmap_1(sK2,sK3))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f3810,f4109])).

fof(f4109,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,k5_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3657])).

fof(f3657,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k5_tmap_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3656])).

fof(f3656,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k5_tmap_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3364])).

fof(f3364,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r2_hidden(X1,k5_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_tmap_1)).

fof(f3810,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f3680])).

fof(f4961,plain,(
    ~ r2_hidden(sK3,k5_tmap_1(sK2,sK3)) ),
    inference(forward_demodulation,[],[f4960,f4691])).

fof(f4691,plain,(
    k5_tmap_1(sK2,sK3) = u1_pre_topc(k6_tmap_1(sK2,sK3)) ),
    inference(subsumption_resolution,[],[f4690,f3807])).

fof(f4690,plain,
    ( k5_tmap_1(sK2,sK3) = u1_pre_topc(k6_tmap_1(sK2,sK3))
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f4689,f3808])).

fof(f4689,plain,
    ( k5_tmap_1(sK2,sK3) = u1_pre_topc(k6_tmap_1(sK2,sK3))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f4504,f3809])).

fof(f4504,plain,
    ( k5_tmap_1(sK2,sK3) = u1_pre_topc(k6_tmap_1(sK2,sK3))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f3810,f3841])).

fof(f3841,plain,(
    ! [X0,X1] :
      ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3502])).

fof(f3502,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3501])).

fof(f3501,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3366])).

fof(f3366,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tmap_1)).

fof(f4960,plain,(
    ~ r2_hidden(sK3,u1_pre_topc(k6_tmap_1(sK2,sK3))) ),
    inference(subsumption_resolution,[],[f4959,f4682])).

fof(f4682,plain,(
    l1_pre_topc(k6_tmap_1(sK2,sK3)) ),
    inference(subsumption_resolution,[],[f4681,f3807])).

fof(f4681,plain,
    ( l1_pre_topc(k6_tmap_1(sK2,sK3))
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f4680,f3808])).

fof(f4680,plain,
    ( l1_pre_topc(k6_tmap_1(sK2,sK3))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f4499,f3809])).

fof(f4499,plain,
    ( l1_pre_topc(k6_tmap_1(sK2,sK3))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f3810,f3836])).

fof(f3836,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3498])).

fof(f3498,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3497])).

fof(f3497,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3345])).

fof(f3345,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_tmap_1)).

fof(f4959,plain,
    ( ~ r2_hidden(sK3,u1_pre_topc(k6_tmap_1(sK2,sK3)))
    | ~ l1_pre_topc(k6_tmap_1(sK2,sK3)) ),
    inference(subsumption_resolution,[],[f4912,f4154])).

fof(f4154,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK2,sK3)))) ),
    inference(forward_demodulation,[],[f3811,f3812])).

fof(f3812,plain,(
    sK3 = sK4 ),
    inference(cnf_transformation,[],[f3680])).

fof(f3811,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK2,sK3)))) ),
    inference(cnf_transformation,[],[f3680])).

fof(f4912,plain,
    ( ~ r2_hidden(sK3,u1_pre_topc(k6_tmap_1(sK2,sK3)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK2,sK3))))
    | ~ l1_pre_topc(k6_tmap_1(sK2,sK3)) ),
    inference(resolution,[],[f4153,f4093])).

fof(f4093,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3792])).

fof(f3792,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f3647])).

fof(f3647,plain,(
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

fof(f4153,plain,(
    ~ v3_pre_topc(sK3,k6_tmap_1(sK2,sK3)) ),
    inference(forward_demodulation,[],[f3813,f3812])).

fof(f3813,plain,(
    ~ v3_pre_topc(sK4,k6_tmap_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f3680])).
%------------------------------------------------------------------------------
