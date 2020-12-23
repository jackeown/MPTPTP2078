%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:26 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 688 expanded)
%              Number of leaves         :   20 ( 148 expanded)
%              Depth                    :   19
%              Number of atoms          :  201 (1637 expanded)
%              Number of equality atoms :   77 ( 228 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f266,plain,(
    $false ),
    inference(subsumption_resolution,[],[f265,f42])).

fof(f42,plain,(
    ~ r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),X1)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),X1)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

fof(f265,plain,(
    r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    inference(superposition,[],[f204,f109])).

fof(f109,plain,(
    k2_tops_1(sK0,sK1) = k3_xboole_0(k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)),sK1) ),
    inference(subsumption_resolution,[],[f108,f75])).

fof(f75,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f40,f70])).

fof(f70,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f66,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f66,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f43,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f43,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f40,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f108,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | k2_tops_1(sK0,sK1) = k3_xboole_0(k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)),sK1) ),
    inference(forward_demodulation,[],[f107,f70])).

fof(f107,plain,
    ( k2_tops_1(sK0,sK1) = k3_xboole_0(k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f106,f89])).

fof(f89,plain,(
    k4_xboole_0(k2_struct_0(sK0),sK1) = k3_subset_1(k2_struct_0(sK0),sK1) ),
    inference(resolution,[],[f75,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f106,plain,
    ( k2_tops_1(sK0,sK1) = k3_xboole_0(k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f105,f94])).

fof(f94,plain,(
    ! [X4] : k9_subset_1(k2_struct_0(sK0),sK1,X4) = k3_xboole_0(X4,sK1) ),
    inference(forward_demodulation,[],[f90,f87])).

fof(f87,plain,(
    ! [X2] : k9_subset_1(k2_struct_0(sK0),X2,sK1) = k3_xboole_0(X2,sK1) ),
    inference(resolution,[],[f75,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f90,plain,(
    ! [X4] : k9_subset_1(k2_struct_0(sK0),X4,sK1) = k9_subset_1(k2_struct_0(sK0),sK1,X4) ),
    inference(resolution,[],[f75,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(f105,plain,
    ( k2_tops_1(sK0,sK1) = k9_subset_1(k2_struct_0(sK0),sK1,k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f104,f70])).

fof(f104,plain,
    ( k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f102,f43])).

fof(f102,plain,
    ( k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f50,f81])).

fof(f81,plain,(
    sK1 = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f80,f75])).

fof(f80,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(forward_demodulation,[],[f79,f70])).

fof(f79,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f78,f43])).

fof(f78,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(resolution,[],[f41,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
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

fof(f41,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_1)).

fof(f204,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(X0,sK1),sK1) ),
    inference(forward_demodulation,[],[f203,f192])).

fof(f192,plain,(
    sK1 = k2_xboole_0(k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f142,f187])).

fof(f187,plain,(
    sK1 = k4_subset_1(k2_struct_0(sK0),k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f179,f186])).

fof(f186,plain,(
    k1_xboole_0 = k4_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f184,f100])).

fof(f100,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,k2_struct_0(sK0)) ),
    inference(resolution,[],[f84,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

fof(f84,plain,(
    r1_tarski(sK1,k2_struct_0(sK0)) ),
    inference(resolution,[],[f75,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f184,plain,(
    k4_xboole_0(sK1,k2_struct_0(sK0)) = k4_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0)) ),
    inference(superposition,[],[f58,f98])).

fof(f98,plain,(
    k2_struct_0(sK0) = k2_xboole_0(sK1,k2_struct_0(sK0)) ),
    inference(resolution,[],[f84,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f58,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f179,plain,(
    sK1 = k4_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0)),sK1) ),
    inference(forward_demodulation,[],[f178,f97])).

fof(f97,plain,(
    sK1 = k3_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)) ),
    inference(forward_demodulation,[],[f93,f89])).

fof(f93,plain,(
    sK1 = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f75,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f178,plain,(
    k3_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)) = k4_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0)),sK1) ),
    inference(forward_demodulation,[],[f177,f150])).

fof(f150,plain,(
    ! [X3] : k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X3) = k4_xboole_0(k2_struct_0(sK0),X3) ),
    inference(resolution,[],[f77,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f77,plain,(
    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f71,f70])).

fof(f71,plain,(
    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f66,f53])).

fof(f53,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(f177,plain,(
    k3_subset_1(k2_struct_0(sK0),k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1)) = k4_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0)),sK1) ),
    inference(forward_demodulation,[],[f175,f151])).

fof(f151,plain,(
    k4_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0)) = k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) ),
    inference(resolution,[],[f77,f62])).

fof(f175,plain,(
    k3_subset_1(k2_struct_0(sK0),k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1)) = k4_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),sK1) ),
    inference(resolution,[],[f92,f77])).

fof(f92,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_struct_0(sK0)))
      | k3_subset_1(k2_struct_0(sK0),k7_subset_1(k2_struct_0(sK0),X6,sK1)) = k4_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),X6),sK1) ) ),
    inference(resolution,[],[f75,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_subset_1)).

fof(f142,plain,(
    k2_xboole_0(k1_xboole_0,sK1) = k4_subset_1(k2_struct_0(sK0),k1_xboole_0,sK1) ),
    inference(resolution,[],[f86,f60])).

fof(f60,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f86,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | k2_xboole_0(X1,sK1) = k4_subset_1(k2_struct_0(sK0),X1,sK1) ) ),
    inference(resolution,[],[f75,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f203,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(X0,k2_xboole_0(k1_xboole_0,sK1)),sK1) ),
    inference(forward_demodulation,[],[f201,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

fof(f201,plain,(
    ! [X0] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,k1_xboole_0),k3_xboole_0(X0,sK1)),sK1) ),
    inference(superposition,[],[f44,f192])).

fof(f44,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:34:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (26253)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.53  % (26253)Refutation not found, incomplete strategy% (26253)------------------------------
% 0.22/0.53  % (26253)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (26269)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.22/0.53  % (26261)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.53  % (26253)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (26253)Memory used [KB]: 6140
% 0.22/0.53  % (26253)Time elapsed: 0.109 s
% 0.22/0.53  % (26253)------------------------------
% 0.22/0.53  % (26253)------------------------------
% 0.22/0.54  % (26267)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.22/0.54  % (26269)Refutation not found, incomplete strategy% (26269)------------------------------
% 0.22/0.54  % (26269)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (26269)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (26269)Memory used [KB]: 10618
% 0.22/0.54  % (26269)Time elapsed: 0.119 s
% 0.22/0.54  % (26269)------------------------------
% 0.22/0.54  % (26269)------------------------------
% 0.22/0.54  % (26260)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.22/0.54  % (26251)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.55  % (26254)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.55  % (26268)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.22/0.55  % (26249)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.55  % (26254)Refutation not found, incomplete strategy% (26254)------------------------------
% 0.22/0.55  % (26254)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (26254)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (26254)Memory used [KB]: 10618
% 0.22/0.55  % (26254)Time elapsed: 0.121 s
% 0.22/0.55  % (26254)------------------------------
% 0.22/0.55  % (26254)------------------------------
% 0.22/0.55  % (26249)Refutation not found, incomplete strategy% (26249)------------------------------
% 0.22/0.55  % (26249)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (26249)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (26249)Memory used [KB]: 10618
% 0.22/0.55  % (26249)Time elapsed: 0.114 s
% 0.22/0.55  % (26249)------------------------------
% 0.22/0.55  % (26249)------------------------------
% 0.22/0.55  % (26246)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.55  % (26259)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.22/0.55  % (26250)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.56  % (26247)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.56  % (26262)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.22/0.56  % (26267)Refutation found. Thanks to Tanya!
% 0.22/0.56  % SZS status Theorem for theBenchmark
% 0.22/0.56  % SZS output start Proof for theBenchmark
% 0.22/0.56  fof(f266,plain,(
% 0.22/0.56    $false),
% 0.22/0.56    inference(subsumption_resolution,[],[f265,f42])).
% 0.22/0.56  fof(f42,plain,(
% 0.22/0.56    ~r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 0.22/0.56    inference(cnf_transformation,[],[f24])).
% 0.22/0.56  fof(f24,plain,(
% 0.22/0.56    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),X1) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.22/0.56    inference(flattening,[],[f23])).
% 0.22/0.56  fof(f23,plain,(
% 0.22/0.56    ? [X0] : (? [X1] : ((~r1_tarski(k2_tops_1(X0,X1),X1) & v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f22])).
% 0.22/0.56  fof(f22,negated_conjecture,(
% 0.22/0.56    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 0.22/0.56    inference(negated_conjecture,[],[f21])).
% 0.22/0.56  fof(f21,conjecture,(
% 0.22/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).
% 0.22/0.56  fof(f265,plain,(
% 0.22/0.56    r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 0.22/0.56    inference(superposition,[],[f204,f109])).
% 0.22/0.56  fof(f109,plain,(
% 0.22/0.56    k2_tops_1(sK0,sK1) = k3_xboole_0(k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)),sK1)),
% 0.22/0.56    inference(subsumption_resolution,[],[f108,f75])).
% 0.22/0.56  fof(f75,plain,(
% 0.22/0.56    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.22/0.56    inference(backward_demodulation,[],[f40,f70])).
% 0.22/0.56  fof(f70,plain,(
% 0.22/0.56    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.22/0.56    inference(resolution,[],[f66,f54])).
% 0.22/0.56  fof(f54,plain,(
% 0.22/0.56    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f30])).
% 0.22/0.56  fof(f30,plain,(
% 0.22/0.56    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f16])).
% 0.22/0.56  fof(f16,axiom,(
% 0.22/0.56    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.56  fof(f66,plain,(
% 0.22/0.56    l1_struct_0(sK0)),
% 0.22/0.56    inference(resolution,[],[f43,f55])).
% 0.22/0.56  fof(f55,plain,(
% 0.22/0.56    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f31])).
% 0.22/0.56  fof(f31,plain,(
% 0.22/0.56    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f18])).
% 0.22/0.56  fof(f18,axiom,(
% 0.22/0.56    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.56  fof(f43,plain,(
% 0.22/0.56    l1_pre_topc(sK0)),
% 0.22/0.56    inference(cnf_transformation,[],[f24])).
% 0.22/0.56  fof(f40,plain,(
% 0.22/0.56    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.56    inference(cnf_transformation,[],[f24])).
% 0.22/0.56  fof(f108,plain,(
% 0.22/0.56    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | k2_tops_1(sK0,sK1) = k3_xboole_0(k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)),sK1)),
% 0.22/0.56    inference(forward_demodulation,[],[f107,f70])).
% 0.22/0.56  fof(f107,plain,(
% 0.22/0.56    k2_tops_1(sK0,sK1) = k3_xboole_0(k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),sK1)),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.56    inference(forward_demodulation,[],[f106,f89])).
% 0.22/0.56  fof(f89,plain,(
% 0.22/0.56    k4_xboole_0(k2_struct_0(sK0),sK1) = k3_subset_1(k2_struct_0(sK0),sK1)),
% 0.22/0.56    inference(resolution,[],[f75,f62])).
% 0.22/0.56  fof(f62,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f36])).
% 0.22/0.56  fof(f36,plain,(
% 0.22/0.56    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f7])).
% 0.22/0.56  fof(f7,axiom,(
% 0.22/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.22/0.56  fof(f106,plain,(
% 0.22/0.56    k2_tops_1(sK0,sK1) = k3_xboole_0(k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.56    inference(forward_demodulation,[],[f105,f94])).
% 0.22/0.56  fof(f94,plain,(
% 0.22/0.56    ( ! [X4] : (k9_subset_1(k2_struct_0(sK0),sK1,X4) = k3_xboole_0(X4,sK1)) )),
% 0.22/0.56    inference(forward_demodulation,[],[f90,f87])).
% 0.22/0.56  fof(f87,plain,(
% 0.22/0.56    ( ! [X2] : (k9_subset_1(k2_struct_0(sK0),X2,sK1) = k3_xboole_0(X2,sK1)) )),
% 0.22/0.56    inference(resolution,[],[f75,f59])).
% 0.22/0.56  fof(f59,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f34])).
% 0.22/0.56  fof(f34,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f11])).
% 0.22/0.56  fof(f11,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.22/0.56  fof(f90,plain,(
% 0.22/0.56    ( ! [X4] : (k9_subset_1(k2_struct_0(sK0),X4,sK1) = k9_subset_1(k2_struct_0(sK0),sK1,X4)) )),
% 0.22/0.56    inference(resolution,[],[f75,f63])).
% 0.22/0.56  fof(f63,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f37])).
% 0.22/0.56  fof(f37,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f6])).
% 0.22/0.56  fof(f6,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).
% 0.22/0.56  fof(f105,plain,(
% 0.22/0.56    k2_tops_1(sK0,sK1) = k9_subset_1(k2_struct_0(sK0),sK1,k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.56    inference(forward_demodulation,[],[f104,f70])).
% 0.22/0.56  fof(f104,plain,(
% 0.22/0.56    k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.56    inference(subsumption_resolution,[],[f102,f43])).
% 0.22/0.56  fof(f102,plain,(
% 0.22/0.56    k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.56    inference(superposition,[],[f50,f81])).
% 0.22/0.56  fof(f81,plain,(
% 0.22/0.56    sK1 = k2_pre_topc(sK0,sK1)),
% 0.22/0.56    inference(subsumption_resolution,[],[f80,f75])).
% 0.22/0.56  fof(f80,plain,(
% 0.22/0.56    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | sK1 = k2_pre_topc(sK0,sK1)),
% 0.22/0.56    inference(forward_demodulation,[],[f79,f70])).
% 0.22/0.56  fof(f79,plain,(
% 0.22/0.56    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = k2_pre_topc(sK0,sK1)),
% 0.22/0.56    inference(subsumption_resolution,[],[f78,f43])).
% 0.22/0.56  fof(f78,plain,(
% 0.22/0.56    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = k2_pre_topc(sK0,sK1)),
% 0.22/0.56    inference(resolution,[],[f41,f52])).
% 0.22/0.56  fof(f52,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1) )),
% 0.22/0.56    inference(cnf_transformation,[],[f28])).
% 0.22/0.56  fof(f28,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.56    inference(flattening,[],[f27])).
% 0.22/0.56  fof(f27,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f19])).
% 0.22/0.56  fof(f19,axiom,(
% 0.22/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.22/0.56  fof(f41,plain,(
% 0.22/0.56    v4_pre_topc(sK1,sK0)),
% 0.22/0.56    inference(cnf_transformation,[],[f24])).
% 0.22/0.56  fof(f50,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f26])).
% 0.22/0.56  fof(f26,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f20])).
% 0.22/0.56  fof(f20,axiom,(
% 0.22/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_1)).
% 0.22/0.56  fof(f204,plain,(
% 0.22/0.56    ( ! [X0] : (r1_tarski(k3_xboole_0(X0,sK1),sK1)) )),
% 0.22/0.56    inference(forward_demodulation,[],[f203,f192])).
% 0.22/0.56  fof(f192,plain,(
% 0.22/0.56    sK1 = k2_xboole_0(k1_xboole_0,sK1)),
% 0.22/0.56    inference(backward_demodulation,[],[f142,f187])).
% 0.22/0.56  fof(f187,plain,(
% 0.22/0.56    sK1 = k4_subset_1(k2_struct_0(sK0),k1_xboole_0,sK1)),
% 0.22/0.56    inference(backward_demodulation,[],[f179,f186])).
% 0.22/0.56  fof(f186,plain,(
% 0.22/0.56    k1_xboole_0 = k4_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0))),
% 0.22/0.56    inference(forward_demodulation,[],[f184,f100])).
% 0.22/0.56  fof(f100,plain,(
% 0.22/0.56    k1_xboole_0 = k4_xboole_0(sK1,k2_struct_0(sK0))),
% 0.22/0.56    inference(resolution,[],[f84,f45])).
% 0.22/0.56  fof(f45,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.22/0.56    inference(cnf_transformation,[],[f4])).
% 0.22/0.56  fof(f4,axiom,(
% 0.22/0.56    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).
% 0.22/0.56  fof(f84,plain,(
% 0.22/0.56    r1_tarski(sK1,k2_struct_0(sK0))),
% 0.22/0.56    inference(resolution,[],[f75,f48])).
% 0.22/0.56  fof(f48,plain,(
% 0.22/0.56    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f14])).
% 0.22/0.56  fof(f14,axiom,(
% 0.22/0.56    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.56  fof(f184,plain,(
% 0.22/0.56    k4_xboole_0(sK1,k2_struct_0(sK0)) = k4_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0))),
% 0.22/0.56    inference(superposition,[],[f58,f98])).
% 0.22/0.56  fof(f98,plain,(
% 0.22/0.56    k2_struct_0(sK0) = k2_xboole_0(sK1,k2_struct_0(sK0))),
% 0.22/0.56    inference(resolution,[],[f84,f49])).
% 0.22/0.56  fof(f49,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.22/0.56    inference(cnf_transformation,[],[f25])).
% 0.22/0.56  fof(f25,plain,(
% 0.22/0.56    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.56    inference(ennf_transformation,[],[f1])).
% 0.22/0.56  fof(f1,axiom,(
% 0.22/0.56    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.22/0.56  fof(f58,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f5])).
% 0.22/0.56  fof(f5,axiom,(
% 0.22/0.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 0.22/0.56  fof(f179,plain,(
% 0.22/0.56    sK1 = k4_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0)),sK1)),
% 0.22/0.56    inference(forward_demodulation,[],[f178,f97])).
% 0.22/0.56  fof(f97,plain,(
% 0.22/0.56    sK1 = k3_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1))),
% 0.22/0.56    inference(forward_demodulation,[],[f93,f89])).
% 0.22/0.56  fof(f93,plain,(
% 0.22/0.56    sK1 = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1))),
% 0.22/0.56    inference(resolution,[],[f75,f65])).
% 0.22/0.56  fof(f65,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.22/0.56    inference(cnf_transformation,[],[f39])).
% 0.22/0.56  fof(f39,plain,(
% 0.22/0.56    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f8])).
% 0.22/0.56  fof(f8,axiom,(
% 0.22/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.22/0.56  fof(f178,plain,(
% 0.22/0.56    k3_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)) = k4_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0)),sK1)),
% 0.22/0.56    inference(forward_demodulation,[],[f177,f150])).
% 0.22/0.56  fof(f150,plain,(
% 0.22/0.56    ( ! [X3] : (k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X3) = k4_xboole_0(k2_struct_0(sK0),X3)) )),
% 0.22/0.56    inference(resolution,[],[f77,f61])).
% 0.22/0.56  fof(f61,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f35])).
% 0.22/0.56  fof(f35,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f10])).
% 0.22/0.56  fof(f10,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.22/0.56  fof(f77,plain,(
% 0.22/0.56    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.22/0.56    inference(forward_demodulation,[],[f71,f70])).
% 0.22/0.56  fof(f71,plain,(
% 0.22/0.56    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.56    inference(resolution,[],[f66,f53])).
% 0.22/0.56  fof(f53,plain,(
% 0.22/0.56    ( ! [X0] : (~l1_struct_0(X0) | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f29])).
% 0.22/0.56  fof(f29,plain,(
% 0.22/0.56    ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f17])).
% 0.22/0.56  fof(f17,axiom,(
% 0.22/0.56    ! [X0] : (l1_struct_0(X0) => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).
% 0.22/0.56  fof(f177,plain,(
% 0.22/0.56    k3_subset_1(k2_struct_0(sK0),k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1)) = k4_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0)),sK1)),
% 0.22/0.56    inference(forward_demodulation,[],[f175,f151])).
% 0.22/0.56  fof(f151,plain,(
% 0.22/0.56    k4_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0)) = k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0))),
% 0.22/0.56    inference(resolution,[],[f77,f62])).
% 0.22/0.56  fof(f175,plain,(
% 0.22/0.56    k3_subset_1(k2_struct_0(sK0),k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1)) = k4_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),sK1)),
% 0.22/0.56    inference(resolution,[],[f92,f77])).
% 0.22/0.56  fof(f92,plain,(
% 0.22/0.56    ( ! [X6] : (~m1_subset_1(X6,k1_zfmisc_1(k2_struct_0(sK0))) | k3_subset_1(k2_struct_0(sK0),k7_subset_1(k2_struct_0(sK0),X6,sK1)) = k4_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),X6),sK1)) )),
% 0.22/0.56    inference(resolution,[],[f75,f64])).
% 0.22/0.56  fof(f64,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f38])).
% 0.22/0.56  fof(f38,plain,(
% 0.22/0.56    ! [X0,X1] : (! [X2] : (k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f12])).
% 0.22/0.56  fof(f12,axiom,(
% 0.22/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_subset_1)).
% 0.22/0.56  fof(f142,plain,(
% 0.22/0.56    k2_xboole_0(k1_xboole_0,sK1) = k4_subset_1(k2_struct_0(sK0),k1_xboole_0,sK1)),
% 0.22/0.56    inference(resolution,[],[f86,f60])).
% 0.22/0.56  fof(f60,plain,(
% 0.22/0.56    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f13])).
% 0.22/0.56  fof(f13,axiom,(
% 0.22/0.56    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.22/0.56  fof(f86,plain,(
% 0.22/0.56    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | k2_xboole_0(X1,sK1) = k4_subset_1(k2_struct_0(sK0),X1,sK1)) )),
% 0.22/0.56    inference(resolution,[],[f75,f56])).
% 0.22/0.56  fof(f56,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f33])).
% 0.22/0.56  fof(f33,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.56    inference(flattening,[],[f32])).
% 0.22/0.56  fof(f32,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.22/0.56    inference(ennf_transformation,[],[f9])).
% 0.22/0.56  fof(f9,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.22/0.56  fof(f203,plain,(
% 0.22/0.56    ( ! [X0] : (r1_tarski(k3_xboole_0(X0,k2_xboole_0(k1_xboole_0,sK1)),sK1)) )),
% 0.22/0.56    inference(forward_demodulation,[],[f201,f57])).
% 0.22/0.56  fof(f57,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f2])).
% 0.22/0.56  fof(f2,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).
% 0.22/0.56  fof(f201,plain,(
% 0.22/0.56    ( ! [X0] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,k1_xboole_0),k3_xboole_0(X0,sK1)),sK1)) )),
% 0.22/0.56    inference(superposition,[],[f44,f192])).
% 0.22/0.56  fof(f44,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f3])).
% 0.22/0.56  fof(f3,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).
% 0.22/0.56  % SZS output end Proof for theBenchmark
% 0.22/0.56  % (26267)------------------------------
% 0.22/0.56  % (26267)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (26267)Termination reason: Refutation
% 0.22/0.56  
% 0.22/0.56  % (26267)Memory used [KB]: 1791
% 0.22/0.56  % (26267)Time elapsed: 0.135 s
% 0.22/0.56  % (26267)------------------------------
% 0.22/0.56  % (26267)------------------------------
% 0.22/0.56  % (26245)Success in time 0.203 s
%------------------------------------------------------------------------------
