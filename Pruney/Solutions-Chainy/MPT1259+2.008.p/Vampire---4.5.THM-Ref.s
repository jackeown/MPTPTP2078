%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:31 EST 2020

% Result     : Theorem 2.36s
% Output     : Refutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 467 expanded)
%              Number of leaves         :   14 ( 101 expanded)
%              Depth                    :   14
%              Number of atoms          :  155 (1265 expanded)
%              Number of equality atoms :   40 ( 290 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2726,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2696,f2725])).

fof(f2725,plain,(
    ~ r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k2_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f2724,f2694])).

fof(f2694,plain,(
    k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f2693,f307])).

fof(f307,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f113,f301])).

fof(f301,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f288,f299])).

fof(f299,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) ),
    inference(forward_demodulation,[],[f287,f76])).

fof(f76,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(unit_resulting_resolution,[],[f70,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f70,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f287,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k3_subset_1(X0,X0) ),
    inference(unit_resulting_resolution,[],[f72,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f72,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f70,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f288,plain,(
    ! [X0] : k3_subset_1(X0,k3_subset_1(X0,X0)) = X0 ),
    inference(unit_resulting_resolution,[],[f72,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f113,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f65,f68])).

fof(f65,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f2693,plain,(
    k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k4_xboole_0(k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f2691,f726])).

fof(f726,plain,(
    m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f48,f165,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f165,plain,(
    m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f48,f150,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f150,plain,(
    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f48,f45,f52])).

fof(f45,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_tops_1(X0,k2_tops_1(X0,X1)) != k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_tops_1(X0,k2_tops_1(X0,X1)) != k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => k2_tops_1(X0,k2_tops_1(X0,X1)) = k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,k2_tops_1(X0,X1)) = k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_tops_1)).

fof(f48,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f2691,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k4_xboole_0(k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k1_xboole_0)
    | ~ m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f508,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f508,plain,(
    k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f498,f165])).

fof(f498,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k1_xboole_0)
    | ~ m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f215,f193])).

fof(f193,plain,(
    k1_xboole_0 = k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f47,f48,f45,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l80_tops_1)).

fof(f47,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f215,plain,(
    ! [X0] :
      ( k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f54,f48])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(f2724,plain,(
    ~ r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k2_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f2695,f727])).

fof(f727,plain,(
    r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) ),
    inference(unit_resulting_resolution,[],[f48,f165,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

fof(f2695,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))))
    | ~ r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k2_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    inference(backward_demodulation,[],[f84,f2694])).

fof(f84,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))))
    | ~ r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k2_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    inference(extensionality_resolution,[],[f51,f46])).

fof(f46,plain,(
    k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f27])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f2696,plain,(
    r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k2_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    inference(backward_demodulation,[],[f177,f2694])).

fof(f177,plain,(
    r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k2_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f48,f150,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tops_1(X0,k2_tops_1(X0,X1)),k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,k2_tops_1(X0,X1)),k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k2_tops_1(X0,k2_tops_1(X0,X1)),k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_tops_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:17:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (22893)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.50  % (22899)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.50  % (22889)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.51  % (22908)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (22882)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.51  % (22885)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (22892)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.52  % (22907)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.52  % (22904)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.52  % (22900)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.52  % (22881)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (22891)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.52  % (22902)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.52  % (22887)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (22883)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (22888)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (22894)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.53  % (22909)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.53  % (22910)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.53  % (22884)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (22903)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.53  % (22896)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (22905)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.54  % (22911)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (22897)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.54  % (22901)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.54  % (22890)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.55  % (22906)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.55  % (22898)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.55  % (22895)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 2.36/0.71  % (22901)Refutation found. Thanks to Tanya!
% 2.36/0.71  % SZS status Theorem for theBenchmark
% 2.36/0.72  % SZS output start Proof for theBenchmark
% 2.36/0.72  fof(f2726,plain,(
% 2.36/0.72    $false),
% 2.36/0.72    inference(subsumption_resolution,[],[f2696,f2725])).
% 2.36/0.72  fof(f2725,plain,(
% 2.36/0.72    ~r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k2_tops_1(sK0,k2_tops_1(sK0,sK1)))),
% 2.36/0.72    inference(forward_demodulation,[],[f2724,f2694])).
% 2.36/0.72  fof(f2694,plain,(
% 2.36/0.72    k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))),
% 2.36/0.72    inference(forward_demodulation,[],[f2693,f307])).
% 2.36/0.72  fof(f307,plain,(
% 2.36/0.72    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.36/0.72    inference(backward_demodulation,[],[f113,f301])).
% 2.36/0.72  fof(f301,plain,(
% 2.36/0.72    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 2.36/0.72    inference(backward_demodulation,[],[f288,f299])).
% 2.36/0.72  fof(f299,plain,(
% 2.36/0.72    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,X0)) )),
% 2.36/0.72    inference(forward_demodulation,[],[f287,f76])).
% 2.36/0.72  fof(f76,plain,(
% 2.36/0.72    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 2.36/0.72    inference(unit_resulting_resolution,[],[f70,f62])).
% 2.36/0.72  fof(f62,plain,(
% 2.36/0.72    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 2.36/0.72    inference(cnf_transformation,[],[f2])).
% 2.36/0.72  fof(f2,axiom,(
% 2.36/0.72    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.36/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.36/0.72  fof(f70,plain,(
% 2.36/0.72    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.36/0.72    inference(equality_resolution,[],[f50])).
% 2.36/0.72  fof(f50,plain,(
% 2.36/0.72    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.36/0.72    inference(cnf_transformation,[],[f1])).
% 2.36/0.72  fof(f1,axiom,(
% 2.36/0.72    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.36/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.36/0.72  fof(f287,plain,(
% 2.36/0.72    ( ! [X0] : (k4_xboole_0(X0,X0) = k3_subset_1(X0,X0)) )),
% 2.36/0.72    inference(unit_resulting_resolution,[],[f72,f68])).
% 2.36/0.72  fof(f68,plain,(
% 2.36/0.72    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 2.36/0.72    inference(cnf_transformation,[],[f43])).
% 2.36/0.72  fof(f43,plain,(
% 2.36/0.72    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.36/0.72    inference(ennf_transformation,[],[f9])).
% 2.36/0.72  fof(f9,axiom,(
% 2.36/0.72    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.36/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 2.36/0.72  fof(f72,plain,(
% 2.36/0.72    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 2.36/0.72    inference(unit_resulting_resolution,[],[f70,f57])).
% 2.36/0.72  fof(f57,plain,(
% 2.36/0.72    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.36/0.72    inference(cnf_transformation,[],[f15])).
% 2.36/0.72  fof(f15,axiom,(
% 2.36/0.72    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.36/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 2.36/0.72  fof(f288,plain,(
% 2.36/0.72    ( ! [X0] : (k3_subset_1(X0,k3_subset_1(X0,X0)) = X0) )),
% 2.36/0.72    inference(unit_resulting_resolution,[],[f72,f67])).
% 2.36/0.72  fof(f67,plain,(
% 2.36/0.72    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.36/0.72    inference(cnf_transformation,[],[f42])).
% 2.36/0.72  fof(f42,plain,(
% 2.36/0.72    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.36/0.72    inference(ennf_transformation,[],[f11])).
% 2.36/0.72  fof(f11,axiom,(
% 2.36/0.72    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 2.36/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 2.36/0.72  fof(f113,plain,(
% 2.36/0.72    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0)) )),
% 2.36/0.72    inference(unit_resulting_resolution,[],[f65,f68])).
% 2.36/0.72  fof(f65,plain,(
% 2.36/0.72    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.36/0.72    inference(cnf_transformation,[],[f14])).
% 2.36/0.72  fof(f14,axiom,(
% 2.36/0.72    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.36/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 2.36/0.72  fof(f2693,plain,(
% 2.36/0.72    k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k4_xboole_0(k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k1_xboole_0)),
% 2.36/0.72    inference(subsumption_resolution,[],[f2691,f726])).
% 2.36/0.72  fof(f726,plain,(
% 2.36/0.72    m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.36/0.72    inference(unit_resulting_resolution,[],[f48,f165,f59])).
% 2.36/0.72  fof(f59,plain,(
% 2.36/0.72    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.36/0.72    inference(cnf_transformation,[],[f36])).
% 2.36/0.73  fof(f36,plain,(
% 2.36/0.73    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.36/0.73    inference(flattening,[],[f35])).
% 2.36/0.73  fof(f35,plain,(
% 2.36/0.73    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.36/0.73    inference(ennf_transformation,[],[f17])).
% 2.36/0.73  fof(f17,axiom,(
% 2.36/0.73    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.36/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 2.36/0.73  fof(f165,plain,(
% 2.36/0.73    m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.36/0.73    inference(unit_resulting_resolution,[],[f48,f150,f52])).
% 2.36/0.73  fof(f52,plain,(
% 2.36/0.73    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.36/0.73    inference(cnf_transformation,[],[f29])).
% 2.36/0.73  fof(f29,plain,(
% 2.36/0.73    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.36/0.73    inference(flattening,[],[f28])).
% 2.36/0.73  fof(f28,plain,(
% 2.36/0.73    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.36/0.73    inference(ennf_transformation,[],[f19])).
% 2.36/0.73  fof(f19,axiom,(
% 2.36/0.73    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.36/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 2.36/0.73  fof(f150,plain,(
% 2.36/0.73    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.36/0.73    inference(unit_resulting_resolution,[],[f48,f45,f52])).
% 2.36/0.73  fof(f45,plain,(
% 2.36/0.73    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.36/0.73    inference(cnf_transformation,[],[f27])).
% 2.36/0.73  fof(f27,plain,(
% 2.36/0.73    ? [X0] : (? [X1] : (k2_tops_1(X0,k2_tops_1(X0,X1)) != k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.36/0.73    inference(flattening,[],[f26])).
% 2.36/0.73  fof(f26,plain,(
% 2.36/0.73    ? [X0] : (? [X1] : (k2_tops_1(X0,k2_tops_1(X0,X1)) != k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.36/0.73    inference(ennf_transformation,[],[f25])).
% 2.36/0.73  fof(f25,negated_conjecture,(
% 2.36/0.73    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,k2_tops_1(X0,X1)) = k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))))),
% 2.36/0.73    inference(negated_conjecture,[],[f24])).
% 2.36/0.73  fof(f24,conjecture,(
% 2.36/0.73    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,k2_tops_1(X0,X1)) = k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))))),
% 2.36/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_tops_1)).
% 2.36/0.73  fof(f48,plain,(
% 2.36/0.73    l1_pre_topc(sK0)),
% 2.36/0.73    inference(cnf_transformation,[],[f27])).
% 2.36/0.73  fof(f2691,plain,(
% 2.36/0.73    k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k4_xboole_0(k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k1_xboole_0) | ~m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.36/0.73    inference(superposition,[],[f508,f66])).
% 2.36/0.73  fof(f66,plain,(
% 2.36/0.73    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.36/0.73    inference(cnf_transformation,[],[f41])).
% 2.36/0.73  fof(f41,plain,(
% 2.36/0.73    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.36/0.73    inference(ennf_transformation,[],[f12])).
% 2.36/0.73  fof(f12,axiom,(
% 2.36/0.73    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 2.36/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 2.36/0.73  fof(f508,plain,(
% 2.36/0.73    k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k1_xboole_0)),
% 2.36/0.73    inference(subsumption_resolution,[],[f498,f165])).
% 2.36/0.73  fof(f498,plain,(
% 2.36/0.73    k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k1_xboole_0) | ~m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.36/0.73    inference(superposition,[],[f215,f193])).
% 2.36/0.73  fof(f193,plain,(
% 2.36/0.73    k1_xboole_0 = k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))),
% 2.36/0.73    inference(unit_resulting_resolution,[],[f47,f48,f45,f53])).
% 2.36/0.73  fof(f53,plain,(
% 2.36/0.73    ( ! [X0,X1] : (k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0)) )),
% 2.36/0.73    inference(cnf_transformation,[],[f31])).
% 2.36/0.73  fof(f31,plain,(
% 2.36/0.73    ! [X0] : (! [X1] : (k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.36/0.73    inference(flattening,[],[f30])).
% 2.36/0.73  fof(f30,plain,(
% 2.36/0.73    ! [X0] : (! [X1] : (k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.36/0.73    inference(ennf_transformation,[],[f21])).
% 2.36/0.73  fof(f21,axiom,(
% 2.36/0.73    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))))),
% 2.36/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l80_tops_1)).
% 2.36/0.73  fof(f47,plain,(
% 2.36/0.73    v2_pre_topc(sK0)),
% 2.36/0.73    inference(cnf_transformation,[],[f27])).
% 2.36/0.73  fof(f215,plain,(
% 2.36/0.73    ( ! [X0] : (k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.36/0.73    inference(resolution,[],[f54,f48])).
% 2.36/0.73  fof(f54,plain,(
% 2.36/0.73    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))) )),
% 2.36/0.73    inference(cnf_transformation,[],[f32])).
% 2.36/0.73  fof(f32,plain,(
% 2.36/0.73    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.36/0.73    inference(ennf_transformation,[],[f20])).
% 2.36/0.73  fof(f20,axiom,(
% 2.36/0.73    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 2.36/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).
% 2.36/0.73  fof(f2724,plain,(
% 2.36/0.73    ~r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k2_tops_1(sK0,k2_tops_1(sK0,sK1)))),
% 2.36/0.73    inference(subsumption_resolution,[],[f2695,f727])).
% 2.36/0.73  fof(f727,plain,(
% 2.36/0.73    r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))))),
% 2.36/0.73    inference(unit_resulting_resolution,[],[f48,f165,f60])).
% 2.36/0.73  fof(f60,plain,(
% 2.36/0.73    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(X1,k2_pre_topc(X0,X1))) )),
% 2.36/0.73    inference(cnf_transformation,[],[f37])).
% 2.36/0.73  fof(f37,plain,(
% 2.36/0.73    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.36/0.73    inference(ennf_transformation,[],[f18])).
% 2.36/0.73  fof(f18,axiom,(
% 2.36/0.73    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 2.36/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).
% 2.36/0.73  fof(f2695,plain,(
% 2.36/0.73    ~r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) | ~r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k2_tops_1(sK0,k2_tops_1(sK0,sK1)))),
% 2.36/0.73    inference(backward_demodulation,[],[f84,f2694])).
% 2.36/0.73  fof(f84,plain,(
% 2.36/0.73    ~r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) | ~r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k2_tops_1(sK0,k2_tops_1(sK0,sK1)))),
% 2.36/0.73    inference(extensionality_resolution,[],[f51,f46])).
% 2.36/0.73  fof(f46,plain,(
% 2.36/0.73    k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))),
% 2.36/0.73    inference(cnf_transformation,[],[f27])).
% 2.36/0.73  fof(f51,plain,(
% 2.36/0.73    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 2.36/0.73    inference(cnf_transformation,[],[f1])).
% 2.36/0.73  fof(f2696,plain,(
% 2.36/0.73    r1_tarski(k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k2_tops_1(sK0,k2_tops_1(sK0,sK1)))),
% 2.36/0.73    inference(backward_demodulation,[],[f177,f2694])).
% 2.36/0.73  fof(f177,plain,(
% 2.36/0.73    r1_tarski(k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k2_tops_1(sK0,k2_tops_1(sK0,sK1)))),
% 2.36/0.73    inference(unit_resulting_resolution,[],[f48,f150,f56])).
% 2.36/0.73  fof(f56,plain,(
% 2.36/0.73    ( ! [X0,X1] : (r1_tarski(k2_tops_1(X0,k2_tops_1(X0,X1)),k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.36/0.73    inference(cnf_transformation,[],[f34])).
% 2.36/0.73  fof(f34,plain,(
% 2.36/0.73    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,k2_tops_1(X0,X1)),k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.36/0.73    inference(ennf_transformation,[],[f23])).
% 2.36/0.73  fof(f23,axiom,(
% 2.36/0.73    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_tops_1(X0,k2_tops_1(X0,X1)),k2_tops_1(X0,X1))))),
% 2.36/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_tops_1)).
% 2.36/0.73  % SZS output end Proof for theBenchmark
% 2.36/0.73  % (22901)------------------------------
% 2.36/0.73  % (22901)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.36/0.73  % (22901)Termination reason: Refutation
% 2.36/0.73  
% 2.36/0.73  % (22901)Memory used [KB]: 2814
% 2.36/0.73  % (22901)Time elapsed: 0.299 s
% 2.36/0.73  % (22901)------------------------------
% 2.36/0.73  % (22901)------------------------------
% 2.88/0.73  % (22880)Success in time 0.371 s
%------------------------------------------------------------------------------
