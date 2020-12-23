%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1257+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:14 EST 2020

% Result     : Theorem 4.97s
% Output     : Refutation 4.97s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 341 expanded)
%              Number of leaves         :   14 ( 117 expanded)
%              Depth                    :   12
%              Number of atoms          :  153 ( 967 expanded)
%              Number of equality atoms :   30 (  61 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11366,plain,(
    $false ),
    inference(subsumption_resolution,[],[f11365,f7854])).

fof(f7854,plain,(
    ~ r1_tarski(k1_tops_1(sK0,sK1),k4_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f7734,f7302])).

fof(f7302,plain,(
    k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)) = k4_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f3303,f3113])).

fof(f3113,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f2504])).

fof(f2504,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f462])).

fof(f462,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f3303,plain,(
    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f2696,f2697,f2765])).

fof(f2765,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2260])).

fof(f2260,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2259])).

fof(f2259,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2090])).

fof(f2090,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f2697,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f2532])).

fof(f2532,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f2203,f2531,f2530])).

fof(f2530,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ r1_xboole_0(k1_tops_1(sK0,X1),k2_tops_1(sK0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f2531,plain,
    ( ? [X1] :
        ( ~ r1_xboole_0(k1_tops_1(sK0,X1),k2_tops_1(sK0,X1))
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f2203,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2145])).

fof(f2145,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f2144])).

fof(f2144,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_tops_1)).

fof(f2696,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f2532])).

fof(f7734,plain,(
    ~ r1_tarski(k1_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f2698,f3303,f3312,f3098])).

fof(f3098,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | r1_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f2666])).

fof(f2666,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_xboole_0(X1,X2)
              | ~ r1_tarski(X1,k3_subset_1(X0,X2)) )
            & ( r1_tarski(X1,k3_subset_1(X0,X2))
              | ~ r1_xboole_0(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f2488])).

fof(f2488,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f516])).

fof(f516,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_subset_1)).

fof(f3312,plain,(
    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f2696,f2697,f2775])).

fof(f2775,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2273])).

fof(f2273,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2272])).

fof(f2272,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2089])).

fof(f2089,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(f2698,plain,(
    ~ r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f2532])).

fof(f11365,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),k4_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f11361,f3533])).

fof(f3533,plain,(
    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))) ),
    inference(forward_demodulation,[],[f3325,f3401])).

fof(f3401,plain,(
    k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
    inference(unit_resulting_resolution,[],[f2697,f3113])).

fof(f3325,plain,(
    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    inference(unit_resulting_resolution,[],[f2696,f2697,f2781])).

fof(f2781,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2282])).

fof(f2282,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2087])).

fof(f2087,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

fof(f11361,plain,(
    r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))),k4_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) ),
    inference(backward_demodulation,[],[f11115,f11358])).

fof(f11358,plain,(
    k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k2_xboole_0(k2_tops_1(sK0,sK1),k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(backward_demodulation,[],[f11139,f11357])).

fof(f11357,plain,(
    k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f10593,f3542])).

fof(f3542,plain,(
    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(forward_demodulation,[],[f3307,f3401])).

fof(f3307,plain,(
    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(unit_resulting_resolution,[],[f2696,f2697,f2770])).

fof(f2770,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2266])).

fof(f2266,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2134])).

fof(f2134,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_1)).

fof(f10593,plain,(
    k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))) ),
    inference(unit_resulting_resolution,[],[f2696,f3454,f2769])).

fof(f2769,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2265])).

fof(f2265,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2136])).

fof(f2136,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(f3454,plain,(
    m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f3402,f3401])).

fof(f3402,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f2697,f3114])).

fof(f3114,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f2505])).

fof(f2505,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f466])).

fof(f466,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f11139,plain,(
    k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) = k2_xboole_0(k2_tops_1(sK0,sK1),k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(forward_demodulation,[],[f10729,f2838])).

fof(f2838,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f10729,plain,(
    k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) = k2_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f3303,f3454,f3083])).

fof(f3083,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f2474])).

fof(f2474,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f2473])).

fof(f2473,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f491])).

fof(f491,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f11115,plain,(
    r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_xboole_0(k2_tops_1(sK0,sK1),k4_xboole_0(u1_struct_0(sK0),sK1))),k4_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) ),
    inference(backward_demodulation,[],[f11047,f10741])).

fof(f10741,plain,(
    k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k4_xboole_0(u1_struct_0(sK0),sK1)) = k2_xboole_0(k2_tops_1(sK0,sK1),k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(unit_resulting_resolution,[],[f3303,f3454,f3083])).

fof(f11047,plain,(
    r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k4_xboole_0(u1_struct_0(sK0),sK1))),k4_xboole_0(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f10789,f7302])).

fof(f10789,plain,(
    r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k4_xboole_0(u1_struct_0(sK0),sK1))),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f3303,f3454,f3090])).

fof(f3090,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f2481])).

fof(f2481,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f514])).

fof(f514,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_subset_1)).
%------------------------------------------------------------------------------
