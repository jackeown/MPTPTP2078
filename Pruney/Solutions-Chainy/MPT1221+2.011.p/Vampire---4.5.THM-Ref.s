%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:50 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 787 expanded)
%              Number of leaves         :   12 ( 183 expanded)
%              Depth                    :   24
%              Number of atoms          :  199 (1912 expanded)
%              Number of equality atoms :   34 ( 258 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f196,plain,(
    $false ),
    inference(subsumption_resolution,[],[f195,f189])).

fof(f189,plain,(
    ~ v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0) ),
    inference(duplicate_literal_removal,[],[f188])).

fof(f188,plain,
    ( ~ v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | ~ v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0) ),
    inference(backward_demodulation,[],[f70,f187])).

fof(f187,plain,(
    k3_subset_1(k2_struct_0(sK0),sK1) = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) ),
    inference(subsumption_resolution,[],[f186,f49])).

fof(f49,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f26,f45])).

fof(f45,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f42,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f42,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f27,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f27,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

fof(f26,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f186,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | k3_subset_1(k2_struct_0(sK0),sK1) = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) ),
    inference(subsumption_resolution,[],[f185,f63])).

fof(f63,plain,(
    m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(resolution,[],[f49,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f185,plain,
    ( ~ m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | k3_subset_1(k2_struct_0(sK0),sK1) = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) ),
    inference(subsumption_resolution,[],[f181,f65])).

fof(f65,plain,(
    k2_struct_0(sK0) = k4_subset_1(k2_struct_0(sK0),sK1,k3_subset_1(k2_struct_0(sK0),sK1)) ),
    inference(forward_demodulation,[],[f62,f41])).

fof(f41,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f62,plain,(
    k2_subset_1(k2_struct_0(sK0)) = k4_subset_1(k2_struct_0(sK0),sK1,k3_subset_1(k2_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f49,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

fof(f181,plain,
    ( k2_struct_0(sK0) != k4_subset_1(k2_struct_0(sK0),sK1,k3_subset_1(k2_struct_0(sK0),sK1))
    | ~ m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | k3_subset_1(k2_struct_0(sK0),sK1) = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) ),
    inference(resolution,[],[f141,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k2_struct_0(sK0) != k4_subset_1(k2_struct_0(sK0),X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0) = X1 ) ),
    inference(forward_demodulation,[],[f56,f45])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k2_struct_0(sK0) != k4_subset_1(k2_struct_0(sK0),X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r1_xboole_0(X0,X1)
      | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0) = X1 ) ),
    inference(forward_demodulation,[],[f55,f45])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k2_struct_0(sK0) != k4_subset_1(u1_struct_0(sK0),X0,X1)
      | ~ r1_xboole_0(X0,X1)
      | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0) = X1 ) ),
    inference(forward_demodulation,[],[f54,f45])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_struct_0(sK0) != k4_subset_1(u1_struct_0(sK0),X0,X1)
      | ~ r1_xboole_0(X0,X1)
      | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0) = X1 ) ),
    inference(forward_demodulation,[],[f46,f45])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_struct_0(sK0) != k4_subset_1(u1_struct_0(sK0),X0,X1)
      | ~ r1_xboole_0(X0,X1)
      | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0) = X1 ) ),
    inference(resolution,[],[f42,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_struct_0(X0) != k4_subset_1(u1_struct_0(X0),X1,X2)
      | ~ r1_xboole_0(X1,X2)
      | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2
              | ~ r1_xboole_0(X1,X2)
              | k2_struct_0(X0) != k4_subset_1(u1_struct_0(X0),X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2
              | ~ r1_xboole_0(X1,X2)
              | k2_struct_0(X0) != k4_subset_1(u1_struct_0(X0),X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_xboole_0(X1,X2)
                  & k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,X2) )
               => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_pre_topc)).

fof(f141,plain,(
    r1_xboole_0(sK1,k3_subset_1(k2_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f125,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f125,plain,(
    r1_xboole_0(k3_subset_1(k2_struct_0(sK0),sK1),sK1) ),
    inference(subsumption_resolution,[],[f124,f63])).

fof(f124,plain,
    ( ~ m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | r1_xboole_0(k3_subset_1(k2_struct_0(sK0),sK1),sK1) ),
    inference(forward_demodulation,[],[f123,f41])).

fof(f123,plain,
    ( r1_xboole_0(k3_subset_1(k2_struct_0(sK0),sK1),sK1)
    | ~ m1_subset_1(k2_subset_1(k3_subset_1(k2_struct_0(sK0),sK1)),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f121,f41])).

fof(f121,plain,
    ( r1_xboole_0(k2_subset_1(k3_subset_1(k2_struct_0(sK0),sK1)),sK1)
    | ~ m1_subset_1(k2_subset_1(k3_subset_1(k2_struct_0(sK0),sK1)),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(resolution,[],[f86,f34])).

fof(f34,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f86,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k3_subset_1(k2_struct_0(sK0),sK1)))
      | r1_xboole_0(X1,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(resolution,[],[f59,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f59,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k3_subset_1(k2_struct_0(sK0),sK1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | r1_xboole_0(X1,sK1) ) ),
    inference(resolution,[],[f49,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | r1_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).

fof(f70,plain,
    ( ~ v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1),sK0)
    | ~ v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0) ),
    inference(forward_demodulation,[],[f69,f45])).

fof(f69,plain,
    ( ~ v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) ),
    inference(subsumption_resolution,[],[f68,f49])).

fof(f68,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) ),
    inference(forward_demodulation,[],[f67,f45])).

fof(f67,plain,
    ( ~ v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) ),
    inference(subsumption_resolution,[],[f66,f27])).

fof(f66,plain,
    ( ~ v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) ),
    inference(resolution,[],[f48,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_pre_topc)).

fof(f48,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | ~ v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0) ),
    inference(backward_demodulation,[],[f25,f45])).

fof(f25,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f195,plain,(
    v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0) ),
    inference(forward_demodulation,[],[f194,f187])).

fof(f194,plain,(
    v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) ),
    inference(subsumption_resolution,[],[f192,f49])).

fof(f192,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) ),
    inference(resolution,[],[f190,f53])).

fof(f53,plain,(
    ! [X1] :
      ( ~ v4_pre_topc(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X1),sK0) ) ),
    inference(forward_demodulation,[],[f51,f45])).

fof(f51,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X1),sK0)
      | ~ v4_pre_topc(X1,sK0) ) ),
    inference(backward_demodulation,[],[f44,f45])).

fof(f44,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X1),sK0)
      | ~ v4_pre_topc(X1,sK0) ) ),
    inference(resolution,[],[f27,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | ~ v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f190,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f189,f47])).

fof(f47,plain,
    ( v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | v4_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f24,f45])).

fof(f24,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:12:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.49  % (8981)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.20/0.49  % (8989)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.20/0.52  % (8979)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.20/0.53  % (8974)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.20/0.53  % (8990)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.20/0.53  % (8978)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.53  % (8980)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.53  % (8982)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.20/0.53  % (8980)Refutation not found, incomplete strategy% (8980)------------------------------
% 0.20/0.53  % (8980)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (8980)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (8980)Memory used [KB]: 6140
% 0.20/0.53  % (8980)Time elapsed: 0.113 s
% 0.20/0.53  % (8980)------------------------------
% 0.20/0.53  % (8980)------------------------------
% 0.20/0.54  % (8995)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.20/0.54  % (8988)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.20/0.54  % (8996)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.20/0.54  % (8977)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.20/0.54  % (8994)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.20/0.54  % (8975)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.20/0.54  % (8976)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.54  % (8996)Refutation not found, incomplete strategy% (8996)------------------------------
% 0.20/0.54  % (8996)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (8973)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.20/0.54  % (8996)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (8996)Memory used [KB]: 10618
% 0.20/0.54  % (8996)Time elapsed: 0.119 s
% 0.20/0.54  % (8996)------------------------------
% 0.20/0.54  % (8996)------------------------------
% 0.20/0.54  % (8985)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.20/0.54  % (8994)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  fof(f196,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(subsumption_resolution,[],[f195,f189])).
% 0.20/0.54  fof(f189,plain,(
% 0.20/0.54    ~v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0)),
% 0.20/0.54    inference(duplicate_literal_removal,[],[f188])).
% 0.20/0.54  fof(f188,plain,(
% 0.20/0.54    ~v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | ~v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0)),
% 0.20/0.54    inference(backward_demodulation,[],[f70,f187])).
% 0.20/0.54  fof(f187,plain,(
% 0.20/0.54    k3_subset_1(k2_struct_0(sK0),sK1) = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1)),
% 0.20/0.54    inference(subsumption_resolution,[],[f186,f49])).
% 0.20/0.54  fof(f49,plain,(
% 0.20/0.54    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.20/0.54    inference(backward_demodulation,[],[f26,f45])).
% 0.20/0.54  fof(f45,plain,(
% 0.20/0.54    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.20/0.54    inference(resolution,[],[f42,f36])).
% 0.20/0.54  fof(f36,plain,(
% 0.20/0.54    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f21])).
% 0.20/0.54  fof(f21,plain,(
% 0.20/0.54    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f8])).
% 0.20/0.54  fof(f8,axiom,(
% 0.20/0.54    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.54  fof(f42,plain,(
% 0.20/0.54    l1_struct_0(sK0)),
% 0.20/0.54    inference(resolution,[],[f27,f37])).
% 0.20/0.54  fof(f37,plain,(
% 0.20/0.54    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f22])).
% 0.20/0.54  fof(f22,plain,(
% 0.20/0.54    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f10])).
% 0.20/0.54  fof(f10,axiom,(
% 0.20/0.54    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.54  fof(f27,plain,(
% 0.20/0.54    l1_pre_topc(sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f14])).
% 0.20/0.54  fof(f14,plain,(
% 0.20/0.54    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f13])).
% 0.20/0.54  fof(f13,negated_conjecture,(
% 0.20/0.54    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.20/0.54    inference(negated_conjecture,[],[f12])).
% 0.20/0.54  fof(f12,conjecture,(
% 0.20/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).
% 0.20/0.54  fof(f26,plain,(
% 0.20/0.54    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.54    inference(cnf_transformation,[],[f14])).
% 0.20/0.54  fof(f186,plain,(
% 0.20/0.54    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | k3_subset_1(k2_struct_0(sK0),sK1) = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1)),
% 0.20/0.54    inference(subsumption_resolution,[],[f185,f63])).
% 0.20/0.54  fof(f63,plain,(
% 0.20/0.54    m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.20/0.54    inference(resolution,[],[f49,f33])).
% 0.20/0.54  fof(f33,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f18])).
% 0.20/0.54  fof(f18,plain,(
% 0.20/0.54    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f4])).
% 0.20/0.54  fof(f4,axiom,(
% 0.20/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.20/0.54  fof(f185,plain,(
% 0.20/0.54    ~m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | k3_subset_1(k2_struct_0(sK0),sK1) = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1)),
% 0.20/0.54    inference(subsumption_resolution,[],[f181,f65])).
% 0.20/0.54  fof(f65,plain,(
% 0.20/0.54    k2_struct_0(sK0) = k4_subset_1(k2_struct_0(sK0),sK1,k3_subset_1(k2_struct_0(sK0),sK1))),
% 0.20/0.54    inference(forward_demodulation,[],[f62,f41])).
% 0.20/0.54  fof(f41,plain,(
% 0.20/0.54    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.20/0.54    inference(cnf_transformation,[],[f2])).
% 0.20/0.54  fof(f2,axiom,(
% 0.20/0.54    ! [X0] : k2_subset_1(X0) = X0),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.20/0.54  fof(f62,plain,(
% 0.20/0.54    k2_subset_1(k2_struct_0(sK0)) = k4_subset_1(k2_struct_0(sK0),sK1,k3_subset_1(k2_struct_0(sK0),sK1))),
% 0.20/0.54    inference(resolution,[],[f49,f32])).
% 0.20/0.54  fof(f32,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f17])).
% 0.20/0.54  fof(f17,plain,(
% 0.20/0.54    ! [X0,X1] : (k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f5])).
% 0.20/0.54  fof(f5,axiom,(
% 0.20/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).
% 0.20/0.54  fof(f181,plain,(
% 0.20/0.54    k2_struct_0(sK0) != k4_subset_1(k2_struct_0(sK0),sK1,k3_subset_1(k2_struct_0(sK0),sK1)) | ~m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | k3_subset_1(k2_struct_0(sK0),sK1) = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1)),
% 0.20/0.54    inference(resolution,[],[f141,f57])).
% 0.20/0.54  fof(f57,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k2_struct_0(sK0) != k4_subset_1(k2_struct_0(sK0),X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0) = X1) )),
% 0.20/0.54    inference(forward_demodulation,[],[f56,f45])).
% 0.20/0.54  fof(f56,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k2_struct_0(sK0) != k4_subset_1(k2_struct_0(sK0),X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_xboole_0(X0,X1) | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0) = X1) )),
% 0.20/0.54    inference(forward_demodulation,[],[f55,f45])).
% 0.20/0.54  fof(f55,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_struct_0(sK0) != k4_subset_1(u1_struct_0(sK0),X0,X1) | ~r1_xboole_0(X0,X1) | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0) = X1) )),
% 0.20/0.54    inference(forward_demodulation,[],[f54,f45])).
% 0.20/0.54  fof(f54,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k2_struct_0(sK0) != k4_subset_1(u1_struct_0(sK0),X0,X1) | ~r1_xboole_0(X0,X1) | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0) = X1) )),
% 0.20/0.54    inference(forward_demodulation,[],[f46,f45])).
% 0.20/0.54  fof(f46,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k2_struct_0(sK0) != k4_subset_1(u1_struct_0(sK0),X0,X1) | ~r1_xboole_0(X0,X1) | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0) = X1) )),
% 0.20/0.54    inference(resolution,[],[f42,f35])).
% 0.20/0.54  fof(f35,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~l1_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k2_struct_0(X0) != k4_subset_1(u1_struct_0(X0),X1,X2) | ~r1_xboole_0(X1,X2) | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2) )),
% 0.20/0.54    inference(cnf_transformation,[],[f20])).
% 0.20/0.54  fof(f20,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (! [X2] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2 | ~r1_xboole_0(X1,X2) | k2_struct_0(X0) != k4_subset_1(u1_struct_0(X0),X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0))),
% 0.20/0.54    inference(flattening,[],[f19])).
% 0.20/0.54  fof(f19,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (! [X2] : ((k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2 | (~r1_xboole_0(X1,X2) | k2_struct_0(X0) != k4_subset_1(u1_struct_0(X0),X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f11])).
% 0.20/0.54  fof(f11,axiom,(
% 0.20/0.54    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_xboole_0(X1,X2) & k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,X2)) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2))))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_pre_topc)).
% 0.20/0.54  fof(f141,plain,(
% 0.20/0.54    r1_xboole_0(sK1,k3_subset_1(k2_struct_0(sK0),sK1))),
% 0.20/0.54    inference(resolution,[],[f125,f40])).
% 0.20/0.54  fof(f40,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f23])).
% 0.20/0.54  fof(f23,plain,(
% 0.20/0.54    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.20/0.54    inference(ennf_transformation,[],[f1])).
% 0.20/0.54  fof(f1,axiom,(
% 0.20/0.54    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.20/0.54  fof(f125,plain,(
% 0.20/0.54    r1_xboole_0(k3_subset_1(k2_struct_0(sK0),sK1),sK1)),
% 0.20/0.54    inference(subsumption_resolution,[],[f124,f63])).
% 0.20/0.54  fof(f124,plain,(
% 0.20/0.54    ~m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) | r1_xboole_0(k3_subset_1(k2_struct_0(sK0),sK1),sK1)),
% 0.20/0.54    inference(forward_demodulation,[],[f123,f41])).
% 0.20/0.54  fof(f123,plain,(
% 0.20/0.54    r1_xboole_0(k3_subset_1(k2_struct_0(sK0),sK1),sK1) | ~m1_subset_1(k2_subset_1(k3_subset_1(k2_struct_0(sK0),sK1)),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.20/0.54    inference(forward_demodulation,[],[f121,f41])).
% 0.20/0.54  fof(f121,plain,(
% 0.20/0.54    r1_xboole_0(k2_subset_1(k3_subset_1(k2_struct_0(sK0),sK1)),sK1) | ~m1_subset_1(k2_subset_1(k3_subset_1(k2_struct_0(sK0),sK1)),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.20/0.54    inference(resolution,[],[f86,f34])).
% 0.20/0.54  fof(f34,plain,(
% 0.20/0.54    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f3])).
% 0.20/0.54  fof(f3,axiom,(
% 0.20/0.54    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.20/0.54  fof(f86,plain,(
% 0.20/0.54    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k3_subset_1(k2_struct_0(sK0),sK1))) | r1_xboole_0(X1,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 0.20/0.54    inference(resolution,[],[f59,f39])).
% 0.20/0.54  fof(f39,plain,(
% 0.20/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f7])).
% 0.20/0.54  fof(f7,axiom,(
% 0.20/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.54  fof(f59,plain,(
% 0.20/0.54    ( ! [X1] : (~r1_tarski(X1,k3_subset_1(k2_struct_0(sK0),sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | r1_xboole_0(X1,sK1)) )),
% 0.20/0.54    inference(resolution,[],[f49,f30])).
% 0.20/0.54  fof(f30,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | r1_xboole_0(X1,X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f16])).
% 0.20/0.54  fof(f16,plain,(
% 0.20/0.54    ! [X0,X1] : (! [X2] : ((r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f6])).
% 0.20/0.54  fof(f6,axiom,(
% 0.20/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2)))))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).
% 0.20/0.54  fof(f70,plain,(
% 0.20/0.54    ~v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) | ~v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0)),
% 0.20/0.54    inference(forward_demodulation,[],[f69,f45])).
% 0.20/0.54  fof(f69,plain,(
% 0.20/0.54    ~v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | ~v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0)),
% 0.20/0.54    inference(subsumption_resolution,[],[f68,f49])).
% 0.20/0.54  fof(f68,plain,(
% 0.20/0.54    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | ~v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0)),
% 0.20/0.54    inference(forward_demodulation,[],[f67,f45])).
% 0.20/0.54  fof(f67,plain,(
% 0.20/0.54    ~v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0)),
% 0.20/0.54    inference(subsumption_resolution,[],[f66,f27])).
% 0.20/0.54  fof(f66,plain,(
% 0.20/0.54    ~v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0)),
% 0.20/0.54    inference(resolution,[],[f48,f28])).
% 0.20/0.54  fof(f28,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | v4_pre_topc(X1,X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f15])).
% 0.20/0.54  fof(f15,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f9])).
% 0.20/0.54  fof(f9,axiom,(
% 0.20/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0))))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_pre_topc)).
% 0.20/0.54  fof(f48,plain,(
% 0.20/0.54    ~v4_pre_topc(sK1,sK0) | ~v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0)),
% 0.20/0.54    inference(backward_demodulation,[],[f25,f45])).
% 0.20/0.54  fof(f25,plain,(
% 0.20/0.54    ~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~v4_pre_topc(sK1,sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f14])).
% 0.20/0.54  fof(f195,plain,(
% 0.20/0.54    v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0)),
% 0.20/0.54    inference(forward_demodulation,[],[f194,f187])).
% 0.20/0.54  fof(f194,plain,(
% 0.20/0.54    v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1),sK0)),
% 0.20/0.54    inference(subsumption_resolution,[],[f192,f49])).
% 0.20/0.54  fof(f192,plain,(
% 0.20/0.54    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1),sK0)),
% 0.20/0.54    inference(resolution,[],[f190,f53])).
% 0.20/0.54  fof(f53,plain,(
% 0.20/0.54    ( ! [X1] : (~v4_pre_topc(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X1),sK0)) )),
% 0.20/0.54    inference(forward_demodulation,[],[f51,f45])).
% 0.20/0.54  fof(f51,plain,(
% 0.20/0.54    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X1),sK0) | ~v4_pre_topc(X1,sK0)) )),
% 0.20/0.54    inference(backward_demodulation,[],[f44,f45])).
% 0.20/0.54  fof(f44,plain,(
% 0.20/0.54    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X1),sK0) | ~v4_pre_topc(X1,sK0)) )),
% 0.20/0.54    inference(resolution,[],[f27,f29])).
% 0.20/0.54  fof(f29,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f15])).
% 0.20/0.54  fof(f190,plain,(
% 0.20/0.54    v4_pre_topc(sK1,sK0)),
% 0.20/0.54    inference(resolution,[],[f189,f47])).
% 0.20/0.54  fof(f47,plain,(
% 0.20/0.54    v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | v4_pre_topc(sK1,sK0)),
% 0.20/0.54    inference(backward_demodulation,[],[f24,f45])).
% 0.20/0.54  fof(f24,plain,(
% 0.20/0.54    v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | v4_pre_topc(sK1,sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f14])).
% 0.20/0.54  % SZS output end Proof for theBenchmark
% 0.20/0.54  % (8994)------------------------------
% 0.20/0.54  % (8994)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (8994)Termination reason: Refutation
% 0.20/0.54  
% 0.20/0.54  % (8994)Memory used [KB]: 1791
% 0.20/0.54  % (8994)Time elapsed: 0.120 s
% 0.20/0.54  % (8994)------------------------------
% 0.20/0.54  % (8994)------------------------------
% 0.20/0.54  % (8986)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.20/0.54  % (8972)Success in time 0.179 s
%------------------------------------------------------------------------------
