%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1282+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:16 EST 2020

% Result     : Theorem 3.11s
% Output     : Refutation 3.11s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 237 expanded)
%              Number of leaves         :    9 (  73 expanded)
%              Depth                    :   16
%              Number of atoms          :  173 (1128 expanded)
%              Number of equality atoms :   55 ( 431 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4661,plain,(
    $false ),
    inference(global_subsumption,[],[f2881,f4491,f4660])).

fof(f4660,plain,(
    k2_tops_1(sK13,k2_pre_topc(sK13,sK14)) = k2_tops_1(sK13,sK14) ),
    inference(subsumption_resolution,[],[f4659,f2878])).

fof(f2878,plain,(
    l1_pre_topc(sK13) ),
    inference(cnf_transformation,[],[f2668])).

fof(f2668,plain,
    ( ( k2_tops_1(sK13,k2_pre_topc(sK13,sK14)) != k7_subset_1(u1_struct_0(sK13),k2_pre_topc(sK13,sK14),sK14)
      | k2_tops_1(sK13,k2_pre_topc(sK13,sK14)) != k2_tops_1(sK13,sK14) )
    & v6_tops_1(sK14,sK13)
    & m1_subset_1(sK14,k1_zfmisc_1(u1_struct_0(sK13)))
    & l1_pre_topc(sK13) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13,sK14])],[f2251,f2667,f2666])).

fof(f2666,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,k2_pre_topc(X0,X1)) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              | k2_tops_1(X0,X1) != k2_tops_1(X0,k2_pre_topc(X0,X1)) )
            & v6_tops_1(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK13,k2_pre_topc(sK13,X1)) != k7_subset_1(u1_struct_0(sK13),k2_pre_topc(sK13,X1),X1)
            | k2_tops_1(sK13,k2_pre_topc(sK13,X1)) != k2_tops_1(sK13,X1) )
          & v6_tops_1(X1,sK13)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK13))) )
      & l1_pre_topc(sK13) ) ),
    introduced(choice_axiom,[])).

fof(f2667,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK13,k2_pre_topc(sK13,X1)) != k7_subset_1(u1_struct_0(sK13),k2_pre_topc(sK13,X1),X1)
          | k2_tops_1(sK13,k2_pre_topc(sK13,X1)) != k2_tops_1(sK13,X1) )
        & v6_tops_1(X1,sK13)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK13))) )
   => ( ( k2_tops_1(sK13,k2_pre_topc(sK13,sK14)) != k7_subset_1(u1_struct_0(sK13),k2_pre_topc(sK13,sK14),sK14)
        | k2_tops_1(sK13,k2_pre_topc(sK13,sK14)) != k2_tops_1(sK13,sK14) )
      & v6_tops_1(sK14,sK13)
      & m1_subset_1(sK14,k1_zfmisc_1(u1_struct_0(sK13))) ) ),
    introduced(choice_axiom,[])).

fof(f2251,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,k2_pre_topc(X0,X1)) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | k2_tops_1(X0,X1) != k2_tops_1(X0,k2_pre_topc(X0,X1)) )
          & v6_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2250])).

fof(f2250,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,k2_pre_topc(X0,X1)) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | k2_tops_1(X0,X1) != k2_tops_1(X0,k2_pre_topc(X0,X1)) )
          & v6_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2134])).

fof(f2134,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v6_tops_1(X1,X0)
             => ( k2_tops_1(X0,k2_pre_topc(X0,X1)) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
                & k2_tops_1(X0,X1) = k2_tops_1(X0,k2_pre_topc(X0,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f2133])).

fof(f2133,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_tops_1(X1,X0)
           => ( k2_tops_1(X0,k2_pre_topc(X0,X1)) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              & k2_tops_1(X0,X1) = k2_tops_1(X0,k2_pre_topc(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tops_1)).

fof(f4659,plain,
    ( k2_tops_1(sK13,k2_pre_topc(sK13,sK14)) = k2_tops_1(sK13,sK14)
    | ~ l1_pre_topc(sK13) ),
    inference(subsumption_resolution,[],[f4658,f3863])).

fof(f3863,plain,(
    m1_subset_1(k2_pre_topc(sK13,sK14),k1_zfmisc_1(u1_struct_0(sK13))) ),
    inference(subsumption_resolution,[],[f3647,f2878])).

fof(f3647,plain,
    ( m1_subset_1(k2_pre_topc(sK13,sK14),k1_zfmisc_1(u1_struct_0(sK13)))
    | ~ l1_pre_topc(sK13) ),
    inference(resolution,[],[f2879,f2901])).

fof(f2901,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2271])).

fof(f2271,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2270])).

fof(f2270,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1780])).

fof(f1780,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f2879,plain,(
    m1_subset_1(sK14,k1_zfmisc_1(u1_struct_0(sK13))) ),
    inference(cnf_transformation,[],[f2668])).

fof(f4658,plain,
    ( k2_tops_1(sK13,k2_pre_topc(sK13,sK14)) = k2_tops_1(sK13,sK14)
    | ~ m1_subset_1(k2_pre_topc(sK13,sK14),k1_zfmisc_1(u1_struct_0(sK13)))
    | ~ l1_pre_topc(sK13) ),
    inference(subsumption_resolution,[],[f4482,f4649])).

fof(f4649,plain,(
    v5_tops_1(k2_pre_topc(sK13,sK14),sK13) ),
    inference(subsumption_resolution,[],[f4648,f2878])).

fof(f4648,plain,
    ( v5_tops_1(k2_pre_topc(sK13,sK14),sK13)
    | ~ l1_pre_topc(sK13) ),
    inference(subsumption_resolution,[],[f4483,f3863])).

fof(f4483,plain,
    ( v5_tops_1(k2_pre_topc(sK13,sK14),sK13)
    | ~ m1_subset_1(k2_pre_topc(sK13,sK14),k1_zfmisc_1(u1_struct_0(sK13)))
    | ~ l1_pre_topc(sK13) ),
    inference(trivial_inequality_removal,[],[f4480])).

fof(f4480,plain,
    ( k2_pre_topc(sK13,sK14) != k2_pre_topc(sK13,sK14)
    | v5_tops_1(k2_pre_topc(sK13,sK14),sK13)
    | ~ m1_subset_1(k2_pre_topc(sK13,sK14),k1_zfmisc_1(u1_struct_0(sK13)))
    | ~ l1_pre_topc(sK13) ),
    inference(superposition,[],[f3232,f3635])).

fof(f3635,plain,(
    sK14 = k1_tops_1(sK13,k2_pre_topc(sK13,sK14)) ),
    inference(subsumption_resolution,[],[f3634,f2878])).

fof(f3634,plain,
    ( sK14 = k1_tops_1(sK13,k2_pre_topc(sK13,sK14))
    | ~ l1_pre_topc(sK13) ),
    inference(subsumption_resolution,[],[f3631,f2879])).

fof(f3631,plain,
    ( sK14 = k1_tops_1(sK13,k2_pre_topc(sK13,sK14))
    | ~ m1_subset_1(sK14,k1_zfmisc_1(u1_struct_0(sK13)))
    | ~ l1_pre_topc(sK13) ),
    inference(resolution,[],[f2880,f2931])).

fof(f2931,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1
      | ~ v6_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2691])).

fof(f2691,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v6_tops_1(X1,X0)
              | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1 )
            & ( k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1
              | ~ v6_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f2287])).

fof(f2287,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_tops_1(X1,X0)
          <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2097])).

fof(f2097,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_tops_1(X1,X0)
          <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_tops_1)).

fof(f2880,plain,(
    v6_tops_1(sK14,sK13) ),
    inference(cnf_transformation,[],[f2668])).

fof(f3232,plain,(
    ! [X0,X1] :
      ( v5_tops_1(X1,X0)
      | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2810])).

fof(f2810,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_tops_1(X1,X0)
              | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1 )
            & ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
              | ~ v5_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f2505])).

fof(f2505,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2096])).

fof(f2096,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tops_1)).

fof(f4482,plain,
    ( k2_tops_1(sK13,k2_pre_topc(sK13,sK14)) = k2_tops_1(sK13,sK14)
    | ~ v5_tops_1(k2_pre_topc(sK13,sK14),sK13)
    | ~ m1_subset_1(k2_pre_topc(sK13,sK14),k1_zfmisc_1(u1_struct_0(sK13)))
    | ~ l1_pre_topc(sK13) ),
    inference(superposition,[],[f3234,f3635])).

fof(f3234,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k2_tops_1(X0,k1_tops_1(X0,X1))
      | ~ v5_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2509])).

fof(f2509,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k2_tops_1(X0,k1_tops_1(X0,X1))
          | ~ v5_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2508])).

fof(f2508,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k2_tops_1(X0,k1_tops_1(X0,X1))
          | ~ v5_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2131])).

fof(f2131,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
           => k2_tops_1(X0,X1) = k2_tops_1(X0,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_tops_1)).

fof(f4491,plain,(
    k2_tops_1(sK13,k2_pre_topc(sK13,sK14)) = k7_subset_1(u1_struct_0(sK13),k2_pre_topc(sK13,sK14),sK14) ),
    inference(forward_demodulation,[],[f4490,f3862])).

fof(f3862,plain,(
    k2_pre_topc(sK13,sK14) = k2_pre_topc(sK13,k2_pre_topc(sK13,sK14)) ),
    inference(subsumption_resolution,[],[f3646,f2878])).

fof(f3646,plain,
    ( k2_pre_topc(sK13,sK14) = k2_pre_topc(sK13,k2_pre_topc(sK13,sK14))
    | ~ l1_pre_topc(sK13) ),
    inference(resolution,[],[f2879,f2900])).

fof(f2900,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2269])).

fof(f2269,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2268])).

fof(f2268,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1809])).

fof(f1809,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).

fof(f4490,plain,(
    k2_tops_1(sK13,k2_pre_topc(sK13,sK14)) = k7_subset_1(u1_struct_0(sK13),k2_pre_topc(sK13,k2_pre_topc(sK13,sK14)),sK14) ),
    inference(subsumption_resolution,[],[f4489,f2878])).

fof(f4489,plain,
    ( k2_tops_1(sK13,k2_pre_topc(sK13,sK14)) = k7_subset_1(u1_struct_0(sK13),k2_pre_topc(sK13,k2_pre_topc(sK13,sK14)),sK14)
    | ~ l1_pre_topc(sK13) ),
    inference(subsumption_resolution,[],[f4468,f3863])).

fof(f4468,plain,
    ( k2_tops_1(sK13,k2_pre_topc(sK13,sK14)) = k7_subset_1(u1_struct_0(sK13),k2_pre_topc(sK13,k2_pre_topc(sK13,sK14)),sK14)
    | ~ m1_subset_1(k2_pre_topc(sK13,sK14),k1_zfmisc_1(u1_struct_0(sK13)))
    | ~ l1_pre_topc(sK13) ),
    inference(superposition,[],[f2898,f3635])).

fof(f2898,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2266])).

fof(f2266,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2118])).

fof(f2118,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(f2881,plain,
    ( k2_tops_1(sK13,k2_pre_topc(sK13,sK14)) != k7_subset_1(u1_struct_0(sK13),k2_pre_topc(sK13,sK14),sK14)
    | k2_tops_1(sK13,k2_pre_topc(sK13,sK14)) != k2_tops_1(sK13,sK14) ),
    inference(cnf_transformation,[],[f2668])).
%------------------------------------------------------------------------------
