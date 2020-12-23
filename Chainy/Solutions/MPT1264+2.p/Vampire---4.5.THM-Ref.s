%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1264+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:14 EST 2020

% Result     : Theorem 17.35s
% Output     : Refutation 17.35s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 335 expanded)
%              Number of leaves         :   21 ( 122 expanded)
%              Depth                    :   15
%              Number of atoms          :  299 (1852 expanded)
%              Number of equality atoms :   74 ( 344 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f23852,plain,(
    $false ),
    inference(subsumption_resolution,[],[f23851,f5550])).

fof(f5550,plain,(
    k2_pre_topc(sK6,sK8) != k2_pre_topc(sK6,k3_xboole_0(sK7,sK8)) ),
    inference(forward_demodulation,[],[f5543,f2824])).

fof(f2824,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f5543,plain,(
    k2_pre_topc(sK6,sK8) != k2_pre_topc(sK6,k3_xboole_0(sK8,sK7)) ),
    inference(backward_demodulation,[],[f2674,f5523])).

fof(f5523,plain,(
    ! [X0] : k3_xboole_0(X0,sK7) = k9_subset_1(u1_struct_0(sK6),X0,sK7) ),
    inference(unit_resulting_resolution,[],[f2670,f2676])).

fof(f2676,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f2170])).

fof(f2170,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f496])).

fof(f496,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f2670,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f2495])).

fof(f2495,plain,
    ( k2_pre_topc(sK6,sK8) != k2_pre_topc(sK6,k9_subset_1(u1_struct_0(sK6),sK8,sK7))
    & v3_pre_topc(sK8,sK6)
    & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6)))
    & v1_tops_1(sK7,sK6)
    & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    & l1_pre_topc(sK6)
    & v2_pre_topc(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f2168,f2494,f2493,f2492])).

fof(f2492,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
                & v3_pre_topc(X2,X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & v1_tops_1(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(sK6,X2) != k2_pre_topc(sK6,k9_subset_1(u1_struct_0(sK6),X2,X1))
              & v3_pre_topc(X2,sK6)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6))) )
          & v1_tops_1(X1,sK6)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) )
      & l1_pre_topc(sK6)
      & v2_pre_topc(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f2493,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k2_pre_topc(sK6,X2) != k2_pre_topc(sK6,k9_subset_1(u1_struct_0(sK6),X2,X1))
            & v3_pre_topc(X2,sK6)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6))) )
        & v1_tops_1(X1,sK6)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) )
   => ( ? [X2] :
          ( k2_pre_topc(sK6,X2) != k2_pre_topc(sK6,k9_subset_1(u1_struct_0(sK6),X2,sK7))
          & v3_pre_topc(X2,sK6)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6))) )
      & v1_tops_1(sK7,sK6)
      & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ) ),
    introduced(choice_axiom,[])).

fof(f2494,plain,
    ( ? [X2] :
        ( k2_pre_topc(sK6,X2) != k2_pre_topc(sK6,k9_subset_1(u1_struct_0(sK6),X2,sK7))
        & v3_pre_topc(X2,sK6)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6))) )
   => ( k2_pre_topc(sK6,sK8) != k2_pre_topc(sK6,k9_subset_1(u1_struct_0(sK6),sK8,sK7))
      & v3_pre_topc(sK8,sK6)
      & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) ) ),
    introduced(choice_axiom,[])).

fof(f2168,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
              & v3_pre_topc(X2,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f2167])).

fof(f2167,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
              & v3_pre_topc(X2,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2161])).

fof(f2161,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v1_tops_1(X1,X0)
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( v3_pre_topc(X2,X0)
                   => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f2160])).

fof(f2160,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( v3_pre_topc(X2,X0)
                 => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_tops_1)).

fof(f2674,plain,(
    k2_pre_topc(sK6,sK8) != k2_pre_topc(sK6,k9_subset_1(u1_struct_0(sK6),sK8,sK7)) ),
    inference(cnf_transformation,[],[f2495])).

fof(f23851,plain,(
    k2_pre_topc(sK6,sK8) = k2_pre_topc(sK6,k3_xboole_0(sK7,sK8)) ),
    inference(forward_demodulation,[],[f23620,f3495])).

fof(f3495,plain,(
    sK8 = k3_xboole_0(sK8,u1_struct_0(sK6)) ),
    inference(unit_resulting_resolution,[],[f3301,f2819])).

fof(f2819,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f2270])).

fof(f2270,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f86])).

fof(f86,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f3301,plain,(
    r1_tarski(sK8,u1_struct_0(sK6)) ),
    inference(unit_resulting_resolution,[],[f2672,f2848])).

fof(f2848,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2572])).

fof(f2572,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f2672,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f2495])).

fof(f23620,plain,(
    k2_pre_topc(sK6,k3_xboole_0(sK7,sK8)) = k2_pre_topc(sK6,k3_xboole_0(sK8,u1_struct_0(sK6))) ),
    inference(backward_demodulation,[],[f9424,f23531])).

fof(f23531,plain,(
    u1_struct_0(sK6) = k2_struct_0(sK6) ),
    inference(forward_demodulation,[],[f23530,f13659])).

fof(f13659,plain,(
    u1_struct_0(sK6) = k2_pre_topc(sK6,u1_struct_0(sK6)) ),
    inference(unit_resulting_resolution,[],[f2669,f7161,f3310,f2725])).

fof(f2725,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f2206])).

fof(f2206,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2205])).

fof(f2205,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1843])).

fof(f1843,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f3310,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f3106,f2849])).

fof(f2849,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2572])).

fof(f3106,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f2858])).

fof(f2858,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2582])).

fof(f2582,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f2581])).

fof(f2581,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f7161,plain,(
    v4_pre_topc(u1_struct_0(sK6),sK6) ),
    inference(forward_demodulation,[],[f7158,f4863])).

fof(f4863,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f4848,f3636])).

fof(f3636,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(unit_resulting_resolution,[],[f2989,f2948])).

fof(f2948,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f2612])).

fof(f2612,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f153])).

fof(f153,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f2989,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f131])).

fof(f131,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f4848,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f3090,f2888])).

fof(f2888,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f2321])).

fof(f2321,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f462])).

fof(f462,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f3090,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f522])).

fof(f522,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f7158,plain,(
    v4_pre_topc(k3_subset_1(u1_struct_0(sK6),k1_xboole_0),sK6) ),
    inference(unit_resulting_resolution,[],[f2669,f6807,f3090,f2757])).

fof(f2757,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ),
    inference(cnf_transformation,[],[f2537])).

fof(f2537,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f2228])).

fof(f2228,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2118])).

fof(f2118,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tops_1)).

fof(f6807,plain,(
    v3_pre_topc(k1_xboole_0,sK6) ),
    inference(unit_resulting_resolution,[],[f2668,f2669,f3071,f3090,f2752])).

fof(f2752,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2225])).

fof(f2225,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f2224])).

fof(f2224,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2086])).

fof(f2086,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tops_1)).

fof(f3071,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f2668,plain,(
    v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f2495])).

fof(f2669,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f2495])).

fof(f23530,plain,(
    k2_struct_0(sK6) = k2_pre_topc(sK6,u1_struct_0(sK6)) ),
    inference(unit_resulting_resolution,[],[f2669,f3310,f13693,f2769])).

fof(f2769,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2545])).

fof(f2545,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_pre_topc(X0,X1) != k2_struct_0(X0) )
            & ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f2235])).

fof(f2235,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2089])).

fof(f2089,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

fof(f13693,plain,(
    v1_tops_1(u1_struct_0(sK6),sK6) ),
    inference(unit_resulting_resolution,[],[f2669,f2671,f3300,f2670,f3310,f2768])).

fof(f2768,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r1_tarski(X1,X2)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tops_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f2234])).

fof(f2234,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_1(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ v1_tops_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2233])).

fof(f2233,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_1(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ v1_tops_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2158])).

fof(f2158,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v1_tops_1(X1,X0) )
               => v1_tops_1(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_tops_1)).

fof(f3300,plain,(
    r1_tarski(sK7,u1_struct_0(sK6)) ),
    inference(unit_resulting_resolution,[],[f2670,f2848])).

fof(f2671,plain,(
    v1_tops_1(sK7,sK6) ),
    inference(cnf_transformation,[],[f2495])).

fof(f9424,plain,(
    k2_pre_topc(sK6,k3_xboole_0(sK7,sK8)) = k2_pre_topc(sK6,k3_xboole_0(sK8,k2_struct_0(sK6))) ),
    inference(forward_demodulation,[],[f9423,f2824])).

fof(f9423,plain,(
    k2_pre_topc(sK6,k3_xboole_0(sK8,sK7)) = k2_pre_topc(sK6,k3_xboole_0(sK8,k2_struct_0(sK6))) ),
    inference(forward_demodulation,[],[f9422,f5523])).

fof(f9422,plain,(
    k2_pre_topc(sK6,k9_subset_1(u1_struct_0(sK6),sK8,sK7)) = k2_pre_topc(sK6,k3_xboole_0(sK8,k2_struct_0(sK6))) ),
    inference(forward_demodulation,[],[f9421,f7168])).

fof(f7168,plain,(
    k2_struct_0(sK6) = k2_pre_topc(sK6,sK7) ),
    inference(unit_resulting_resolution,[],[f2669,f2671,f2670,f2769])).

fof(f9421,plain,(
    k2_pre_topc(sK6,k9_subset_1(u1_struct_0(sK6),sK8,sK7)) = k2_pre_topc(sK6,k3_xboole_0(sK8,k2_pre_topc(sK6,sK7))) ),
    inference(forward_demodulation,[],[f9420,f2824])).

fof(f9420,plain,(
    k2_pre_topc(sK6,k9_subset_1(u1_struct_0(sK6),sK8,sK7)) = k2_pre_topc(sK6,k3_xboole_0(k2_pre_topc(sK6,sK7),sK8)) ),
    inference(forward_demodulation,[],[f9395,f5796])).

fof(f5796,plain,(
    ! [X0] : k3_xboole_0(X0,sK8) = k9_subset_1(u1_struct_0(sK6),sK8,X0) ),
    inference(forward_demodulation,[],[f5778,f5524])).

fof(f5524,plain,(
    ! [X0] : k3_xboole_0(X0,sK8) = k9_subset_1(u1_struct_0(sK6),X0,sK8) ),
    inference(unit_resulting_resolution,[],[f2672,f2676])).

fof(f5778,plain,(
    ! [X0] : k9_subset_1(u1_struct_0(sK6),X0,sK8) = k9_subset_1(u1_struct_0(sK6),sK8,X0) ),
    inference(unit_resulting_resolution,[],[f2672,f2675])).

fof(f2675,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f2169])).

fof(f2169,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f454])).

fof(f454,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(f9395,plain,(
    k2_pre_topc(sK6,k9_subset_1(u1_struct_0(sK6),sK8,sK7)) = k2_pre_topc(sK6,k9_subset_1(u1_struct_0(sK6),sK8,k2_pre_topc(sK6,sK7))) ),
    inference(unit_resulting_resolution,[],[f2668,f2669,f2673,f2672,f2670,f2686])).

fof(f2686,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) ) ),
    inference(cnf_transformation,[],[f2181])).

fof(f2181,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)))
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f2180])).

fof(f2180,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)))
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2128])).

fof(f2128,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( v3_pre_topc(X1,X0)
               => k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tops_1)).

fof(f2673,plain,(
    v3_pre_topc(sK8,sK6) ),
    inference(cnf_transformation,[],[f2495])).
%------------------------------------------------------------------------------
