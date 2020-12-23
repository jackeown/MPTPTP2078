%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:08 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 222 expanded)
%              Number of leaves         :   10 (  44 expanded)
%              Depth                    :   20
%              Number of atoms          :  187 ( 932 expanded)
%              Number of equality atoms :   20 (  39 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f303,plain,(
    $false ),
    inference(subsumption_resolution,[],[f302,f53])).

fof(f53,plain,(
    ~ v6_tops_1(k3_xboole_0(sK1,sK2),sK0) ),
    inference(backward_demodulation,[],[f26,f52])).

fof(f52,plain,(
    ! [X2] : k9_subset_1(u1_struct_0(sK0),X2,sK2) = k3_xboole_0(X2,sK2) ),
    inference(resolution,[],[f23,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f23,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v6_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v6_tops_1(X2,X0)
              & v6_tops_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v6_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v6_tops_1(X2,X0)
              & v6_tops_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v6_tops_1(X2,X0)
                    & v6_tops_1(X1,X0) )
                 => v6_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v6_tops_1(X2,X0)
                  & v6_tops_1(X1,X0) )
               => v6_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_tops_1)).

fof(f26,plain,(
    ~ v6_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f302,plain,(
    v6_tops_1(k3_xboole_0(sK1,sK2),sK0) ),
    inference(forward_demodulation,[],[f301,f290])).

fof(f290,plain,(
    k3_xboole_0(sK1,sK2) = k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2)) ),
    inference(forward_demodulation,[],[f289,f52])).

fof(f289,plain,(
    k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2)) ),
    inference(forward_demodulation,[],[f284,f48])).

fof(f48,plain,(
    sK2 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)) ),
    inference(resolution,[],[f23,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f284,plain,(
    k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2)) = k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2))) ),
    inference(resolution,[],[f58,f50])).

fof(f50,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f23,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f58,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k7_subset_1(u1_struct_0(sK0),sK1,X1) = k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),X1)) ) ),
    inference(resolution,[],[f27,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).

fof(f27,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f301,plain,(
    v6_tops_1(k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2)),sK0) ),
    inference(subsumption_resolution,[],[f295,f92])).

fof(f92,plain,(
    ! [X0] : m1_subset_1(k3_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f63,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f63,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(sK1,X0),u1_struct_0(sK0)) ),
    inference(resolution,[],[f54,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

fof(f54,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f27,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f295,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | v6_tops_1(k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2)),sK0) ),
    inference(backward_demodulation,[],[f162,f290])).

fof(f162,plain,
    ( ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v6_tops_1(k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2)),sK0) ),
    inference(subsumption_resolution,[],[f158,f29])).

fof(f29,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f158,plain,
    ( ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v6_tops_1(k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2)),sK0) ),
    inference(resolution,[],[f124,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v6_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_tops_1(X1,X0)
          <=> v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_tops_1(X1,X0)
          <=> v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_tops_1)).

fof(f124,plain,(
    v5_tops_1(k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2))),sK0) ),
    inference(backward_demodulation,[],[f97,f120])).

fof(f120,plain,(
    k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2))) ),
    inference(resolution,[],[f56,f50])).

fof(f56,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,X0)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),X0) ) ),
    inference(resolution,[],[f27,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_subset_1)).

fof(f97,plain,(
    v5_tops_1(k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)),sK0) ),
    inference(subsumption_resolution,[],[f95,f50])).

fof(f95,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | v5_tops_1(k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)),sK0) ),
    inference(resolution,[],[f68,f46])).

fof(f46,plain,(
    v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK2),sK0) ),
    inference(subsumption_resolution,[],[f45,f29])).

fof(f45,plain,
    ( v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK2),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f44,f23])).

fof(f44,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK2),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f25,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v6_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f25,plain,(
    v6_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v5_tops_1(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v5_tops_1(k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),X0),sK0) ) ),
    inference(subsumption_resolution,[],[f67,f28])).

fof(f28,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f67,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0)
      | ~ v5_tops_1(X0,sK0)
      | v5_tops_1(k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),X0),sK0) ) ),
    inference(subsumption_resolution,[],[f66,f57])).

fof(f57,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f27,f34])).

fof(f66,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0)
      | ~ v5_tops_1(X0,sK0)
      | v5_tops_1(k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),X0),sK0) ) ),
    inference(subsumption_resolution,[],[f65,f29])).

fof(f65,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0)
      | ~ v5_tops_1(X0,sK0)
      | v5_tops_1(k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),X0),sK0) ) ),
    inference(resolution,[],[f43,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_tops_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ v5_tops_1(X2,X0)
      | v5_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v5_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
              | ~ v5_tops_1(X2,X0)
              | ~ v5_tops_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v5_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
              | ~ v5_tops_1(X2,X0)
              | ~ v5_tops_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v5_tops_1(X2,X0)
                  & v5_tops_1(X1,X0) )
               => v5_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_tops_1)).

fof(f43,plain,(
    v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(subsumption_resolution,[],[f42,f29])).

fof(f42,plain,
    ( v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f41,f27])).

fof(f41,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f24,f33])).

fof(f24,plain,(
    v6_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:22:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (7023)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.49  % (7032)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.22/0.49  % (7031)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.22/0.50  % (7041)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.22/0.51  % (7024)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.51  % (7028)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.51  % (7027)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.51  % (7032)Refutation not found, incomplete strategy% (7032)------------------------------
% 0.22/0.51  % (7032)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (7032)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (7032)Memory used [KB]: 10618
% 0.22/0.51  % (7032)Time elapsed: 0.104 s
% 0.22/0.51  % (7032)------------------------------
% 0.22/0.51  % (7032)------------------------------
% 0.22/0.51  % (7022)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.51  % (7026)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.51  % (7033)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.22/0.51  % (7045)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.22/0.51  % (7036)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.22/0.51  % (7037)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.52  % (7035)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.22/0.52  % (7029)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (7045)Refutation not found, incomplete strategy% (7045)------------------------------
% 0.22/0.52  % (7045)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (7040)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.22/0.52  % (7034)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.22/0.53  % (7044)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.22/0.53  % (7045)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (7045)Memory used [KB]: 10618
% 0.22/0.53  % (7045)Time elapsed: 0.071 s
% 0.22/0.53  % (7045)------------------------------
% 0.22/0.53  % (7045)------------------------------
% 0.22/0.53  % (7025)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.53  % (7043)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.22/0.53  % (7025)Refutation not found, incomplete strategy% (7025)------------------------------
% 0.22/0.53  % (7025)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (7025)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (7025)Memory used [KB]: 10490
% 0.22/0.53  % (7025)Time elapsed: 0.119 s
% 0.22/0.53  % (7025)------------------------------
% 0.22/0.53  % (7025)------------------------------
% 0.22/0.53  % (7039)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.22/0.54  % (7042)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.54  % (7030)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.54  % (7030)Refutation not found, incomplete strategy% (7030)------------------------------
% 0.22/0.54  % (7030)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (7030)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (7030)Memory used [KB]: 10618
% 0.22/0.54  % (7030)Time elapsed: 0.122 s
% 0.22/0.54  % (7030)------------------------------
% 0.22/0.54  % (7030)------------------------------
% 0.22/0.55  % (7038)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.22/0.56  % (7042)Refutation found. Thanks to Tanya!
% 0.22/0.56  % SZS status Theorem for theBenchmark
% 0.22/0.56  % SZS output start Proof for theBenchmark
% 0.22/0.56  fof(f303,plain,(
% 0.22/0.56    $false),
% 0.22/0.56    inference(subsumption_resolution,[],[f302,f53])).
% 0.22/0.56  fof(f53,plain,(
% 0.22/0.56    ~v6_tops_1(k3_xboole_0(sK1,sK2),sK0)),
% 0.22/0.56    inference(backward_demodulation,[],[f26,f52])).
% 0.22/0.56  fof(f52,plain,(
% 0.22/0.56    ( ! [X2] : (k9_subset_1(u1_struct_0(sK0),X2,sK2) = k3_xboole_0(X2,sK2)) )),
% 0.22/0.56    inference(resolution,[],[f23,f30])).
% 0.22/0.56  fof(f30,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f14])).
% 0.22/0.56  fof(f14,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f4])).
% 0.22/0.56  fof(f4,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.22/0.56  fof(f23,plain,(
% 0.22/0.56    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.56    inference(cnf_transformation,[],[f13])).
% 0.22/0.56  fof(f13,plain,(
% 0.22/0.56    ? [X0] : (? [X1] : (? [X2] : (~v6_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v6_tops_1(X2,X0) & v6_tops_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.56    inference(flattening,[],[f12])).
% 0.22/0.56  fof(f12,plain,(
% 0.22/0.56    ? [X0] : (? [X1] : (? [X2] : ((~v6_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v6_tops_1(X2,X0) & v6_tops_1(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f11])).
% 0.22/0.56  fof(f11,negated_conjecture,(
% 0.22/0.56    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v6_tops_1(X2,X0) & v6_tops_1(X1,X0)) => v6_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.22/0.56    inference(negated_conjecture,[],[f10])).
% 0.22/0.56  fof(f10,conjecture,(
% 0.22/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v6_tops_1(X2,X0) & v6_tops_1(X1,X0)) => v6_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_tops_1)).
% 0.22/0.56  fof(f26,plain,(
% 0.22/0.56    ~v6_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 0.22/0.56    inference(cnf_transformation,[],[f13])).
% 0.22/0.56  fof(f302,plain,(
% 0.22/0.56    v6_tops_1(k3_xboole_0(sK1,sK2),sK0)),
% 0.22/0.56    inference(forward_demodulation,[],[f301,f290])).
% 0.22/0.56  fof(f290,plain,(
% 0.22/0.56    k3_xboole_0(sK1,sK2) = k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2))),
% 0.22/0.56    inference(forward_demodulation,[],[f289,f52])).
% 0.22/0.56  fof(f289,plain,(
% 0.22/0.56    k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2))),
% 0.22/0.56    inference(forward_demodulation,[],[f284,f48])).
% 0.22/0.56  fof(f48,plain,(
% 0.22/0.56    sK2 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2))),
% 0.22/0.56    inference(resolution,[],[f23,f37])).
% 0.22/0.56  fof(f37,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.22/0.56    inference(cnf_transformation,[],[f21])).
% 0.22/0.56  fof(f21,plain,(
% 0.22/0.56    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f3])).
% 0.22/0.56  fof(f3,axiom,(
% 0.22/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.22/0.56  fof(f284,plain,(
% 0.22/0.56    k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2)) = k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)))),
% 0.22/0.56    inference(resolution,[],[f58,f50])).
% 0.22/0.56  fof(f50,plain,(
% 0.22/0.56    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.56    inference(resolution,[],[f23,f34])).
% 0.22/0.56  fof(f34,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f17])).
% 0.22/0.56  fof(f17,plain,(
% 0.22/0.56    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f2])).
% 0.22/0.56  fof(f2,axiom,(
% 0.22/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.22/0.56  fof(f58,plain,(
% 0.22/0.56    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k7_subset_1(u1_struct_0(sK0),sK1,X1) = k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),X1))) )),
% 0.22/0.56    inference(resolution,[],[f27,f31])).
% 0.22/0.56  fof(f31,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f15])).
% 0.22/0.56  fof(f15,plain,(
% 0.22/0.56    ! [X0,X1] : (! [X2] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f5])).
% 0.22/0.56  fof(f5,axiom,(
% 0.22/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).
% 0.22/0.56  fof(f27,plain,(
% 0.22/0.56    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.56    inference(cnf_transformation,[],[f13])).
% 0.22/0.56  fof(f301,plain,(
% 0.22/0.56    v6_tops_1(k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2)),sK0)),
% 0.22/0.56    inference(subsumption_resolution,[],[f295,f92])).
% 0.22/0.56  fof(f92,plain,(
% 0.22/0.56    ( ! [X0] : (m1_subset_1(k3_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.22/0.56    inference(resolution,[],[f63,f39])).
% 0.22/0.56  fof(f39,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f7])).
% 0.22/0.56  fof(f7,axiom,(
% 0.22/0.56    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.56  fof(f63,plain,(
% 0.22/0.56    ( ! [X0] : (r1_tarski(k3_xboole_0(sK1,X0),u1_struct_0(sK0))) )),
% 0.22/0.56    inference(resolution,[],[f54,f38])).
% 0.22/0.56  fof(f38,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k3_xboole_0(X0,X2),X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f22])).
% 0.22/0.56  fof(f22,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 0.22/0.56    inference(ennf_transformation,[],[f1])).
% 0.22/0.56  fof(f1,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).
% 0.22/0.56  fof(f54,plain,(
% 0.22/0.56    r1_tarski(sK1,u1_struct_0(sK0))),
% 0.22/0.56    inference(resolution,[],[f27,f40])).
% 0.22/0.56  fof(f40,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f7])).
% 0.22/0.56  fof(f295,plain,(
% 0.22/0.56    ~m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | v6_tops_1(k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2)),sK0)),
% 0.22/0.56    inference(backward_demodulation,[],[f162,f290])).
% 0.22/0.56  fof(f162,plain,(
% 0.22/0.56    ~m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | v6_tops_1(k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2)),sK0)),
% 0.22/0.56    inference(subsumption_resolution,[],[f158,f29])).
% 0.22/0.56  fof(f29,plain,(
% 0.22/0.56    l1_pre_topc(sK0)),
% 0.22/0.56    inference(cnf_transformation,[],[f13])).
% 0.22/0.56  fof(f158,plain,(
% 0.22/0.56    ~m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v6_tops_1(k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2)),sK0)),
% 0.22/0.56    inference(resolution,[],[f124,f32])).
% 0.22/0.56  fof(f32,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v6_tops_1(X1,X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f16])).
% 0.22/0.56  fof(f16,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : ((v6_tops_1(X1,X0) <=> v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f8])).
% 0.22/0.56  fof(f8,axiom,(
% 0.22/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v6_tops_1(X1,X0) <=> v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_tops_1)).
% 0.22/0.56  fof(f124,plain,(
% 0.22/0.56    v5_tops_1(k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2))),sK0)),
% 0.22/0.56    inference(backward_demodulation,[],[f97,f120])).
% 0.22/0.56  fof(f120,plain,(
% 0.22/0.56    k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2)))),
% 0.22/0.56    inference(resolution,[],[f56,f50])).
% 0.22/0.56  fof(f56,plain,(
% 0.22/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,X0)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),X0)) )),
% 0.22/0.56    inference(resolution,[],[f27,f36])).
% 0.22/0.56  fof(f36,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f20])).
% 0.22/0.56  fof(f20,plain,(
% 0.22/0.56    ! [X0,X1] : (! [X2] : (k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f6])).
% 0.22/0.56  fof(f6,axiom,(
% 0.22/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_subset_1)).
% 0.22/0.56  fof(f97,plain,(
% 0.22/0.56    v5_tops_1(k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)),sK0)),
% 0.22/0.56    inference(subsumption_resolution,[],[f95,f50])).
% 0.22/0.56  fof(f95,plain,(
% 0.22/0.56    ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) | v5_tops_1(k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)),sK0)),
% 0.22/0.56    inference(resolution,[],[f68,f46])).
% 0.22/0.56  fof(f46,plain,(
% 0.22/0.56    v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK2),sK0)),
% 0.22/0.56    inference(subsumption_resolution,[],[f45,f29])).
% 0.22/0.56  fof(f45,plain,(
% 0.22/0.56    v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK2),sK0) | ~l1_pre_topc(sK0)),
% 0.22/0.56    inference(subsumption_resolution,[],[f44,f23])).
% 0.22/0.56  fof(f44,plain,(
% 0.22/0.56    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK2),sK0) | ~l1_pre_topc(sK0)),
% 0.22/0.56    inference(resolution,[],[f25,f33])).
% 0.22/0.56  fof(f33,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~v6_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f16])).
% 0.22/0.56  fof(f25,plain,(
% 0.22/0.56    v6_tops_1(sK2,sK0)),
% 0.22/0.56    inference(cnf_transformation,[],[f13])).
% 0.22/0.56  fof(f68,plain,(
% 0.22/0.56    ( ! [X0] : (~v5_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v5_tops_1(k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),X0),sK0)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f67,f28])).
% 0.22/0.56  fof(f28,plain,(
% 0.22/0.56    v2_pre_topc(sK0)),
% 0.22/0.56    inference(cnf_transformation,[],[f13])).
% 0.22/0.56  fof(f67,plain,(
% 0.22/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | ~v5_tops_1(X0,sK0) | v5_tops_1(k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),X0),sK0)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f66,f57])).
% 0.22/0.56  fof(f57,plain,(
% 0.22/0.56    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.56    inference(resolution,[],[f27,f34])).
% 0.22/0.56  fof(f66,plain,(
% 0.22/0.56    ( ! [X0] : (~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | ~v5_tops_1(X0,sK0) | v5_tops_1(k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),X0),sK0)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f65,f29])).
% 0.22/0.56  fof(f65,plain,(
% 0.22/0.56    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | ~v5_tops_1(X0,sK0) | v5_tops_1(k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),X0),sK0)) )),
% 0.22/0.56    inference(resolution,[],[f43,f35])).
% 0.22/0.56  fof(f35,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~v5_tops_1(X1,X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~v5_tops_1(X2,X0) | v5_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f19])).
% 0.22/0.56  fof(f19,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (! [X2] : (v5_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0) | ~v5_tops_1(X2,X0) | ~v5_tops_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.56    inference(flattening,[],[f18])).
% 0.22/0.56  fof(f18,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (! [X2] : ((v5_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0) | (~v5_tops_1(X2,X0) | ~v5_tops_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f9])).
% 0.22/0.56  fof(f9,axiom,(
% 0.22/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v5_tops_1(X2,X0) & v5_tops_1(X1,X0)) => v5_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_tops_1)).
% 0.22/0.56  fof(f43,plain,(
% 0.22/0.56    v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 0.22/0.56    inference(subsumption_resolution,[],[f42,f29])).
% 0.22/0.56  fof(f42,plain,(
% 0.22/0.56    v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~l1_pre_topc(sK0)),
% 0.22/0.56    inference(subsumption_resolution,[],[f41,f27])).
% 0.22/0.56  fof(f41,plain,(
% 0.22/0.56    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~l1_pre_topc(sK0)),
% 0.22/0.56    inference(resolution,[],[f24,f33])).
% 0.22/0.56  fof(f24,plain,(
% 0.22/0.56    v6_tops_1(sK1,sK0)),
% 0.22/0.56    inference(cnf_transformation,[],[f13])).
% 0.22/0.56  % SZS output end Proof for theBenchmark
% 0.22/0.56  % (7042)------------------------------
% 0.22/0.56  % (7042)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (7042)Termination reason: Refutation
% 0.22/0.56  
% 0.22/0.56  % (7042)Memory used [KB]: 6396
% 0.22/0.56  % (7042)Time elapsed: 0.150 s
% 0.22/0.56  % (7042)------------------------------
% 0.22/0.56  % (7042)------------------------------
% 0.22/0.57  % (7021)Success in time 0.204 s
%------------------------------------------------------------------------------
