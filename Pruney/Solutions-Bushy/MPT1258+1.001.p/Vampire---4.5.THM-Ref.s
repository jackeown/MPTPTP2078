%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1258+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:34 EST 2020

% Result     : Theorem 4.22s
% Output     : Refutation 4.22s
% Verified   : 
% Statistics : Number of formulae       :  155 (1218 expanded)
%              Number of leaves         :   22 ( 296 expanded)
%              Depth                    :   31
%              Number of atoms          :  245 (2466 expanded)
%              Number of equality atoms :   96 ( 680 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10172,plain,(
    $false ),
    inference(subsumption_resolution,[],[f10171,f138])).

fof(f138,plain,(
    k1_tops_1(sK0,sK1) != k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f48,f83])).

fof(f83,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(resolution,[],[f47,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f47,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(f48,plain,(
    k1_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f10171,plain,(
    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f10170,f475])).

fof(f475,plain,(
    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f474,f337])).

fof(f337,plain,(
    k1_tops_1(sK0,sK1) = k3_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f106,f74])).

fof(f74,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f106,plain,(
    k1_tops_1(sK0,sK1) = k3_xboole_0(k1_tops_1(sK0,sK1),sK1) ),
    inference(resolution,[],[f94,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f94,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f79,f49])).

fof(f49,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f79,plain,
    ( ~ l1_pre_topc(sK0)
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(resolution,[],[f47,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(f474,plain,(
    k3_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k4_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f458,f121])).

fof(f121,plain,(
    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) ),
    inference(resolution,[],[f96,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f96,plain,(
    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f81,f49])).

fof(f81,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f47,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(f458,plain,(
    k4_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) = k3_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)))) ),
    inference(resolution,[],[f122,f101])).

fof(f101,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k4_xboole_0(sK1,X1) = k3_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),X1)) ) ),
    inference(forward_demodulation,[],[f100,f74])).

fof(f100,plain,(
    ! [X1] :
      ( k4_xboole_0(sK1,X1) = k3_xboole_0(k3_subset_1(u1_struct_0(sK0),X1),sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(backward_demodulation,[],[f98,f99])).

fof(f99,plain,(
    ! [X2] : k9_subset_1(u1_struct_0(sK0),sK1,X2) = k3_xboole_0(X2,sK1) ),
    inference(backward_demodulation,[],[f86,f87])).

fof(f87,plain,(
    ! [X3] : k9_subset_1(u1_struct_0(sK0),X3,sK1) = k3_xboole_0(X3,sK1) ),
    inference(resolution,[],[f47,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f86,plain,(
    ! [X2] : k9_subset_1(u1_struct_0(sK0),X2,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X2) ),
    inference(resolution,[],[f47,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(f98,plain,(
    ! [X1] :
      ( k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),X1)) = k4_xboole_0(sK1,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(forward_demodulation,[],[f84,f83])).

fof(f84,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k7_subset_1(u1_struct_0(sK0),sK1,X1) = k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),X1)) ) ),
    inference(resolution,[],[f47,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

fof(f122,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f96,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f10170,plain,(
    k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k4_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f10138,f10046])).

fof(f10046,plain,(
    k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k3_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) ),
    inference(resolution,[],[f9932,f101])).

fof(f9932,plain,(
    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f1949,f1994])).

fof(f1994,plain,(
    k2_tops_1(sK0,sK1) = k3_xboole_0(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,sK1)) ),
    inference(superposition,[],[f198,f1291])).

fof(f1291,plain,(
    k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) ),
    inference(backward_demodulation,[],[f97,f1289])).

fof(f1289,plain,(
    k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1267,f95])).

fof(f95,plain,(
    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    inference(subsumption_resolution,[],[f80,f49])).

fof(f80,plain,
    ( ~ l1_pre_topc(sK0)
    | k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    inference(resolution,[],[f47,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

fof(f1267,plain,(
    k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))) ),
    inference(resolution,[],[f256,f64])).

fof(f256,plain,(
    m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f240,f49])).

fof(f240,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f90,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f90,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f47,f65])).

fof(f97,plain,(
    k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    inference(subsumption_resolution,[],[f82,f49])).

fof(f82,plain,
    ( ~ l1_pre_topc(sK0)
    | k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    inference(resolution,[],[f47,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_1)).

fof(f198,plain,(
    ! [X2] : k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X2) = k3_xboole_0(X2,k2_pre_topc(sK0,sK1)) ),
    inference(backward_demodulation,[],[f185,f186])).

fof(f186,plain,(
    ! [X3] : k9_subset_1(u1_struct_0(sK0),X3,k2_pre_topc(sK0,sK1)) = k3_xboole_0(X3,k2_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f93,f62])).

fof(f93,plain,(
    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f78,f49])).

fof(f78,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f47,f56])).

fof(f185,plain,(
    ! [X2] : k9_subset_1(u1_struct_0(sK0),X2,k2_pre_topc(sK0,sK1)) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X2) ),
    inference(resolution,[],[f93,f61])).

fof(f1949,plain,(
    ! [X0] : m1_subset_1(k3_xboole_0(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)),X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f493,f74])).

fof(f493,plain,(
    ! [X4] : m1_subset_1(k3_xboole_0(X4,k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f470,f469])).

fof(f469,plain,(
    ! [X3] : k9_subset_1(u1_struct_0(sK0),X3,k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) = k3_xboole_0(X3,k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) ),
    inference(resolution,[],[f122,f62])).

fof(f470,plain,(
    ! [X4] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),X4,k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f122,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f10138,plain,(
    k4_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) = k3_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) ),
    inference(superposition,[],[f3769,f1994])).

fof(f3769,plain,(
    ! [X1] : k4_xboole_0(sK1,X1) = k3_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),k3_xboole_0(X1,k2_pre_topc(sK0,sK1)))) ),
    inference(backward_demodulation,[],[f909,f3768])).

fof(f3768,plain,(
    ! [X0] : k4_xboole_0(sK1,X0) = k4_xboole_0(sK1,k3_xboole_0(X0,k2_pre_topc(sK0,sK1))) ),
    inference(forward_demodulation,[],[f3766,f71])).

fof(f71,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f3766,plain,(
    ! [X0] : k4_xboole_0(sK1,k3_xboole_0(X0,k2_pre_topc(sK0,sK1))) = k2_xboole_0(k4_xboole_0(sK1,X0),k1_xboole_0) ),
    inference(superposition,[],[f58,f3641])).

fof(f3641,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,k2_pre_topc(sK0,sK1)) ),
    inference(forward_demodulation,[],[f3621,f774])).

fof(f774,plain,(
    k1_xboole_0 = k3_subset_1(sK1,sK1) ),
    inference(forward_demodulation,[],[f765,f769])).

fof(f769,plain,(
    sK1 = k3_subset_1(sK1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f761,f60])).

fof(f60,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f761,plain,(
    k4_xboole_0(sK1,k1_xboole_0) = k3_subset_1(sK1,k1_xboole_0) ),
    inference(resolution,[],[f754,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f754,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f746,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f746,plain,(
    r1_tarski(k1_xboole_0,sK1) ),
    inference(superposition,[],[f735,f75])).

fof(f75,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f735,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(k1_tops_1(sK0,sK1),X0),sK1) ),
    inference(superposition,[],[f718,f74])).

fof(f718,plain,(
    ! [X13] : r1_tarski(k3_xboole_0(X13,k1_tops_1(sK0,sK1)),sK1) ),
    inference(resolution,[],[f152,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f152,plain,(
    ! [X4] : m1_subset_1(k3_xboole_0(X4,k1_tops_1(sK0,sK1)),k1_zfmisc_1(sK1)) ),
    inference(forward_demodulation,[],[f144,f143])).

fof(f143,plain,(
    ! [X3] : k3_xboole_0(X3,k1_tops_1(sK0,sK1)) = k9_subset_1(sK1,X3,k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f108,f62])).

fof(f108,plain,(
    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f94,f66])).

fof(f144,plain,(
    ! [X4] : m1_subset_1(k9_subset_1(sK1,X4,k1_tops_1(sK0,sK1)),k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f108,f63])).

fof(f765,plain,(
    k1_xboole_0 = k3_subset_1(sK1,k3_subset_1(sK1,k1_xboole_0)) ),
    inference(resolution,[],[f754,f64])).

fof(f3621,plain,(
    k4_xboole_0(sK1,k2_pre_topc(sK0,sK1)) = k3_subset_1(sK1,sK1) ),
    inference(superposition,[],[f1976,f135])).

fof(f135,plain,(
    sK1 = k3_xboole_0(sK1,k2_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f92,f70])).

fof(f92,plain,(
    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f77,f49])).

fof(f77,plain,
    ( ~ l1_pre_topc(sK0)
    | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f47,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r1_tarski(X1,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

fof(f1976,plain,(
    ! [X0] : k4_xboole_0(sK1,X0) = k3_subset_1(sK1,k3_xboole_0(sK1,X0)) ),
    inference(backward_demodulation,[],[f1184,f1966])).

fof(f1966,plain,(
    ! [X0] : k4_xboole_0(sK1,X0) = k3_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),k3_xboole_0(sK1,X0))) ),
    inference(superposition,[],[f982,f74])).

fof(f982,plain,(
    ! [X0] : k4_xboole_0(sK1,X0) = k3_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),k3_xboole_0(X0,sK1))) ),
    inference(backward_demodulation,[],[f205,f981])).

fof(f981,plain,(
    ! [X0] : k4_xboole_0(sK1,X0) = k4_xboole_0(sK1,k3_xboole_0(X0,sK1)) ),
    inference(forward_demodulation,[],[f979,f71])).

fof(f979,plain,(
    ! [X0] : k4_xboole_0(sK1,k3_xboole_0(X0,sK1)) = k2_xboole_0(k4_xboole_0(sK1,X0),k1_xboole_0) ),
    inference(superposition,[],[f58,f813])).

fof(f813,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK1) ),
    inference(forward_demodulation,[],[f805,f774])).

fof(f805,plain,(
    k4_xboole_0(sK1,sK1) = k3_subset_1(sK1,sK1) ),
    inference(resolution,[],[f775,f59])).

fof(f775,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    inference(forward_demodulation,[],[f766,f769])).

fof(f766,plain,(
    m1_subset_1(k3_subset_1(sK1,k1_xboole_0),k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f754,f65])).

fof(f205,plain,(
    ! [X0] : k4_xboole_0(sK1,k3_xboole_0(X0,sK1)) = k3_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),k3_xboole_0(X0,sK1))) ),
    inference(resolution,[],[f102,f101])).

fof(f102,plain,(
    ! [X4] : m1_subset_1(k3_xboole_0(X4,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f88,f87])).

fof(f88,plain,(
    ! [X4] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),X4,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f47,f63])).

fof(f1184,plain,(
    ! [X0] : k3_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),k3_xboole_0(sK1,X0))) = k3_subset_1(sK1,k3_xboole_0(sK1,X0)) ),
    inference(backward_demodulation,[],[f568,f1165])).

fof(f1165,plain,(
    ! [X4] : k3_subset_1(sK1,k3_xboole_0(sK1,X4)) = k4_xboole_0(sK1,k3_xboole_0(sK1,X4)) ),
    inference(resolution,[],[f1089,f59])).

fof(f1089,plain,(
    ! [X0] : m1_subset_1(k3_xboole_0(sK1,X0),k1_zfmisc_1(sK1)) ),
    inference(superposition,[],[f856,f74])).

fof(f856,plain,(
    ! [X4] : m1_subset_1(k3_xboole_0(X4,sK1),k1_zfmisc_1(sK1)) ),
    inference(forward_demodulation,[],[f808,f807])).

fof(f807,plain,(
    ! [X3] : k3_xboole_0(X3,sK1) = k9_subset_1(sK1,X3,sK1) ),
    inference(resolution,[],[f775,f62])).

fof(f808,plain,(
    ! [X4] : m1_subset_1(k9_subset_1(sK1,X4,sK1),k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f775,f63])).

fof(f568,plain,(
    ! [X0] : k4_xboole_0(sK1,k3_xboole_0(sK1,X0)) = k3_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),k3_xboole_0(sK1,X0))) ),
    inference(resolution,[],[f221,f101])).

fof(f221,plain,(
    ! [X0] : m1_subset_1(k3_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f102,f74])).

fof(f58,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_xboole_1)).

fof(f909,plain,(
    ! [X1] : k4_xboole_0(sK1,k3_xboole_0(X1,k2_pre_topc(sK0,sK1))) = k3_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),k3_xboole_0(X1,k2_pre_topc(sK0,sK1)))) ),
    inference(resolution,[],[f201,f101])).

fof(f201,plain,(
    ! [X4] : m1_subset_1(k3_xboole_0(X4,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f187,f186])).

fof(f187,plain,(
    ! [X4] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),X4,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f93,f63])).

%------------------------------------------------------------------------------
