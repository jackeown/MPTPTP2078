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
% DateTime   : Thu Dec  3 13:12:39 EST 2020

% Result     : Theorem 2.70s
% Output     : Refutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 808 expanded)
%              Number of leaves         :   14 ( 167 expanded)
%              Depth                    :   21
%              Number of atoms          :  234 (2075 expanded)
%              Number of equality atoms :   34 ( 194 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1402,plain,(
    $false ),
    inference(global_subsumption,[],[f374,f650,f1401])).

fof(f1401,plain,(
    r1_tarski(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k1_tops_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f1400,f227])).

fof(f227,plain,(
    k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k1_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f216,f168])).

fof(f168,plain,(
    k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) ),
    inference(resolution,[],[f118,f80])).

fof(f80,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f45,f79])).

fof(f79,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f75,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f75,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f48,f72])).

fof(f72,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f48,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
          & v3_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
          & v3_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_tops_1(X1,X0)
             => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
           => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_tops_1)).

fof(f45,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f118,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_struct_0(sK0)))
      | k1_tops_1(sK0,X6) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X6))) ) ),
    inference(subsumption_resolution,[],[f111,f48])).

fof(f111,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | k1_tops_1(sK0,X6) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X6))) ) ),
    inference(superposition,[],[f68,f79])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

fof(f216,plain,(
    k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))) ),
    inference(resolution,[],[f147,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f147,plain,(
    m1_subset_1(k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(resolution,[],[f115,f83])).

fof(f83,plain,(
    m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(resolution,[],[f80,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f115,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0)))
      | m1_subset_1(k2_pre_topc(sK0,X2),k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f108,f48])).

fof(f108,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | m1_subset_1(k2_pre_topc(sK0,X2),k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(superposition,[],[f62,f79])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f1400,plain,(
    r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) ),
    inference(subsumption_resolution,[],[f1382,f171])).

fof(f171,plain,(
    r1_tarski(k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)),k3_subset_1(k2_struct_0(sK0),sK1)) ),
    inference(backward_demodulation,[],[f142,f170])).

fof(f170,plain,(
    k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) ),
    inference(forward_demodulation,[],[f169,f84])).

fof(f84,plain,(
    sK1 = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f80,f56])).

fof(f169,plain,(
    k1_tops_1(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1)))) ),
    inference(resolution,[],[f118,f83])).

fof(f142,plain,(
    r1_tarski(k1_tops_1(sK0,k3_subset_1(k2_struct_0(sK0),sK1)),k3_subset_1(k2_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f119,f83])).

fof(f119,plain,(
    ! [X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_struct_0(sK0)))
      | r1_tarski(k1_tops_1(sK0,X7),X7) ) ),
    inference(subsumption_resolution,[],[f112,f48])).

fof(f112,plain,(
    ! [X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | r1_tarski(k1_tops_1(sK0,X7),X7) ) ),
    inference(superposition,[],[f71,f79])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f1382,plain,
    ( r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))
    | ~ r1_tarski(k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)),k3_subset_1(k2_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f415,f83])).

fof(f415,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,X0))
      | ~ r1_tarski(k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)),X0) ) ),
    inference(forward_demodulation,[],[f398,f304])).

fof(f304,plain,(
    k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f303,f183])).

fof(f183,plain,(
    m1_subset_1(k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(resolution,[],[f146,f57])).

fof(f146,plain,(
    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(resolution,[],[f115,f80])).

fof(f303,plain,
    ( ~ m1_subset_1(k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(k2_struct_0(sK0)))
    | k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1))) ),
    inference(forward_demodulation,[],[f302,f79])).

fof(f302,plain,
    ( ~ m1_subset_1(k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f301,f48])).

fof(f301,plain,
    ( ~ m1_subset_1(k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f172,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

fof(f172,plain,(
    v1_tops_1(k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)),sK0) ),
    inference(resolution,[],[f146,f95])).

fof(f95,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)),sK0) ),
    inference(forward_demodulation,[],[f94,f79])).

fof(f94,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | v1_tops_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),sK0) ),
    inference(forward_demodulation,[],[f93,f79])).

fof(f93,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_tops_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),sK0) ),
    inference(subsumption_resolution,[],[f92,f48])).

fof(f92,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_tops_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f78,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_1)).

fof(f78,plain,(
    v2_tops_1(k2_pre_topc(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f77,f48])).

fof(f77,plain,
    ( v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f76,f45])).

fof(f76,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f46,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v3_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tops_1(k2_pre_topc(X0,X1),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tops_1(X1,X0)
          <=> v2_tops_1(k2_pre_topc(X0,X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
          <=> v2_tops_1(k2_pre_topc(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tops_1)).

fof(f46,plain,(
    v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f398,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r1_tarski(k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)),X0)
      | r1_tarski(k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1))),k2_pre_topc(sK0,X0)) ) ),
    inference(resolution,[],[f183,f116])).

fof(f116,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r1_tarski(X3,X4)
      | r1_tarski(k2_pre_topc(sK0,X3),k2_pre_topc(sK0,X4)) ) ),
    inference(subsumption_resolution,[],[f109,f48])).

fof(f109,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r1_tarski(X3,X4)
      | r1_tarski(k2_pre_topc(sK0,X3),k2_pre_topc(sK0,X4)) ) ),
    inference(superposition,[],[f63,f79])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_pre_topc)).

fof(f650,plain,(
    k2_struct_0(sK0) != k3_subset_1(k2_struct_0(sK0),k1_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f153,f227])).

fof(f153,plain,(
    k2_struct_0(sK0) != k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f152,f81])).

fof(f81,plain,(
    ~ v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) ),
    inference(backward_demodulation,[],[f47,f79])).

fof(f47,plain,(
    ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f152,plain,
    ( k2_struct_0(sK0) != k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))
    | v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) ),
    inference(resolution,[],[f113,f83])).

fof(f113,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k2_struct_0(sK0) != k2_pre_topc(sK0,X0)
      | v1_tops_1(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f106,f48])).

fof(f106,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | k2_struct_0(sK0) != k2_pre_topc(sK0,X0)
      | v1_tops_1(X0,sK0) ) ),
    inference(superposition,[],[f49,f79])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k2_struct_0(X0) != k2_pre_topc(X0,X1)
      | v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f374,plain,
    ( ~ r1_tarski(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k1_tops_1(sK0,sK1)))
    | k2_struct_0(sK0) = k3_subset_1(k2_struct_0(sK0),k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f236,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f236,plain,(
    r1_tarski(k3_subset_1(k2_struct_0(sK0),k1_tops_1(sK0,sK1)),k2_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f214,f227])).

fof(f214,plain,(
    r1_tarski(k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)),k2_struct_0(sK0)) ),
    inference(resolution,[],[f147,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:10:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.51  % (23745)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.51  % (23762)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.52  % (23748)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.52  % (23746)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.53  % (23742)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.54  % (23740)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.54  % (23754)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.54  % (23761)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.55  % (23752)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.55  % (23753)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.55  % (23741)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.55  % (23749)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.56  % (23758)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.56  % (23743)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.56  % (23763)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.56  % (23756)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.56  % (23755)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.57  % (23750)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.57  % (23759)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.57  % (23747)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.57  % (23744)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.58  % (23757)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.59  % (23739)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.60  % (23751)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.60  % (23760)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.61  % (23764)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 2.70/0.71  % (23748)Refutation not found, incomplete strategy% (23748)------------------------------
% 2.70/0.71  % (23748)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.70/0.71  % (23748)Termination reason: Refutation not found, incomplete strategy
% 2.70/0.71  
% 2.70/0.71  % (23748)Memory used [KB]: 6140
% 2.70/0.71  % (23748)Time elapsed: 0.278 s
% 2.70/0.71  % (23748)------------------------------
% 2.70/0.71  % (23748)------------------------------
% 2.70/0.72  % (23744)Refutation found. Thanks to Tanya!
% 2.70/0.72  % SZS status Theorem for theBenchmark
% 2.70/0.72  % SZS output start Proof for theBenchmark
% 2.70/0.72  fof(f1402,plain,(
% 2.70/0.72    $false),
% 2.70/0.72    inference(global_subsumption,[],[f374,f650,f1401])).
% 2.70/0.72  fof(f1401,plain,(
% 2.70/0.72    r1_tarski(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k1_tops_1(sK0,sK1)))),
% 2.70/0.72    inference(forward_demodulation,[],[f1400,f227])).
% 2.70/0.72  fof(f227,plain,(
% 2.70/0.72    k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k1_tops_1(sK0,sK1))),
% 2.70/0.72    inference(forward_demodulation,[],[f216,f168])).
% 2.70/0.72  fof(f168,plain,(
% 2.70/0.72    k1_tops_1(sK0,sK1) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))),
% 2.70/0.72    inference(resolution,[],[f118,f80])).
% 2.70/0.72  fof(f80,plain,(
% 2.70/0.72    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 2.70/0.72    inference(backward_demodulation,[],[f45,f79])).
% 2.70/0.72  fof(f79,plain,(
% 2.70/0.72    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 2.70/0.72    inference(resolution,[],[f75,f69])).
% 2.70/0.72  fof(f69,plain,(
% 2.70/0.72    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 2.70/0.72    inference(cnf_transformation,[],[f40])).
% 2.70/0.72  fof(f40,plain,(
% 2.70/0.72    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.70/0.72    inference(ennf_transformation,[],[f11])).
% 2.70/0.72  fof(f11,axiom,(
% 2.70/0.72    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.70/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 2.70/0.72  fof(f75,plain,(
% 2.70/0.72    l1_struct_0(sK0)),
% 2.70/0.72    inference(resolution,[],[f48,f72])).
% 2.70/0.72  fof(f72,plain,(
% 2.70/0.72    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 2.70/0.72    inference(cnf_transformation,[],[f44])).
% 2.70/0.72  fof(f44,plain,(
% 2.70/0.72    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.70/0.72    inference(ennf_transformation,[],[f13])).
% 2.70/0.72  fof(f13,axiom,(
% 2.70/0.72    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.70/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 2.70/0.72  fof(f48,plain,(
% 2.70/0.72    l1_pre_topc(sK0)),
% 2.70/0.72    inference(cnf_transformation,[],[f25])).
% 2.70/0.72  fof(f25,plain,(
% 2.70/0.72    ? [X0] : (? [X1] : (~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) & v3_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.70/0.72    inference(flattening,[],[f24])).
% 2.70/0.72  fof(f24,plain,(
% 2.70/0.72    ? [X0] : (? [X1] : ((~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) & v3_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.70/0.72    inference(ennf_transformation,[],[f23])).
% 2.70/0.72  fof(f23,negated_conjecture,(
% 2.70/0.72    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 2.70/0.72    inference(negated_conjecture,[],[f22])).
% 2.70/0.72  fof(f22,conjecture,(
% 2.70/0.72    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 2.70/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_tops_1)).
% 2.70/0.72  fof(f45,plain,(
% 2.70/0.72    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.70/0.72    inference(cnf_transformation,[],[f25])).
% 2.70/0.72  fof(f118,plain,(
% 2.70/0.72    ( ! [X6] : (~m1_subset_1(X6,k1_zfmisc_1(k2_struct_0(sK0))) | k1_tops_1(sK0,X6) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X6)))) )),
% 2.70/0.72    inference(subsumption_resolution,[],[f111,f48])).
% 2.70/0.72  fof(f111,plain,(
% 2.70/0.72    ( ! [X6] : (~m1_subset_1(X6,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | k1_tops_1(sK0,X6) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X6)))) )),
% 2.70/0.72    inference(superposition,[],[f68,f79])).
% 2.70/0.72  fof(f68,plain,(
% 2.70/0.72    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))) )),
% 2.70/0.72    inference(cnf_transformation,[],[f39])).
% 2.70/0.72  fof(f39,plain,(
% 2.70/0.72    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.70/0.72    inference(ennf_transformation,[],[f16])).
% 2.70/0.72  fof(f16,axiom,(
% 2.70/0.72    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 2.70/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).
% 2.70/0.72  fof(f216,plain,(
% 2.70/0.72    k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))))),
% 2.70/0.72    inference(resolution,[],[f147,f56])).
% 2.70/0.72  fof(f56,plain,(
% 2.70/0.72    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 2.70/0.72    inference(cnf_transformation,[],[f31])).
% 2.70/0.72  fof(f31,plain,(
% 2.70/0.72    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.70/0.72    inference(ennf_transformation,[],[f7])).
% 2.70/0.72  fof(f7,axiom,(
% 2.70/0.72    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 2.70/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 2.70/0.72  fof(f147,plain,(
% 2.70/0.72    m1_subset_1(k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)),k1_zfmisc_1(k2_struct_0(sK0)))),
% 2.70/0.72    inference(resolution,[],[f115,f83])).
% 2.70/0.72  fof(f83,plain,(
% 2.70/0.72    m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))),
% 2.70/0.72    inference(resolution,[],[f80,f57])).
% 2.70/0.72  fof(f57,plain,(
% 2.70/0.72    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 2.70/0.72    inference(cnf_transformation,[],[f32])).
% 2.70/0.72  fof(f32,plain,(
% 2.70/0.72    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.70/0.72    inference(ennf_transformation,[],[f6])).
% 2.70/0.72  fof(f6,axiom,(
% 2.70/0.72    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.70/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 2.70/0.72  fof(f115,plain,(
% 2.70/0.72    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0))) | m1_subset_1(k2_pre_topc(sK0,X2),k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 2.70/0.72    inference(subsumption_resolution,[],[f108,f48])).
% 2.70/0.72  fof(f108,plain,(
% 2.70/0.72    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | m1_subset_1(k2_pre_topc(sK0,X2),k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 2.70/0.72    inference(superposition,[],[f62,f79])).
% 2.70/0.72  fof(f62,plain,(
% 2.70/0.72    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 2.70/0.72    inference(cnf_transformation,[],[f35])).
% 2.70/0.72  fof(f35,plain,(
% 2.70/0.72    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.70/0.72    inference(flattening,[],[f34])).
% 2.70/0.72  fof(f34,plain,(
% 2.70/0.72    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.70/0.72    inference(ennf_transformation,[],[f12])).
% 2.70/0.72  fof(f12,axiom,(
% 2.70/0.72    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.70/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 2.70/0.72  fof(f1400,plain,(
% 2.70/0.72    r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)))),
% 2.70/0.72    inference(subsumption_resolution,[],[f1382,f171])).
% 2.70/0.72  fof(f171,plain,(
% 2.70/0.72    r1_tarski(k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)),k3_subset_1(k2_struct_0(sK0),sK1))),
% 2.70/0.72    inference(backward_demodulation,[],[f142,f170])).
% 2.70/0.72  fof(f170,plain,(
% 2.70/0.72    k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,k3_subset_1(k2_struct_0(sK0),sK1))),
% 2.70/0.72    inference(forward_demodulation,[],[f169,f84])).
% 2.70/0.72  fof(f84,plain,(
% 2.70/0.72    sK1 = k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1))),
% 2.70/0.72    inference(resolution,[],[f80,f56])).
% 2.70/0.72  fof(f169,plain,(
% 2.70/0.72    k1_tops_1(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1))))),
% 2.70/0.72    inference(resolution,[],[f118,f83])).
% 2.70/0.72  fof(f142,plain,(
% 2.70/0.72    r1_tarski(k1_tops_1(sK0,k3_subset_1(k2_struct_0(sK0),sK1)),k3_subset_1(k2_struct_0(sK0),sK1))),
% 2.70/0.72    inference(resolution,[],[f119,f83])).
% 2.70/0.72  fof(f119,plain,(
% 2.70/0.72    ( ! [X7] : (~m1_subset_1(X7,k1_zfmisc_1(k2_struct_0(sK0))) | r1_tarski(k1_tops_1(sK0,X7),X7)) )),
% 2.70/0.72    inference(subsumption_resolution,[],[f112,f48])).
% 2.70/0.72  fof(f112,plain,(
% 2.70/0.72    ( ! [X7] : (~m1_subset_1(X7,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | r1_tarski(k1_tops_1(sK0,X7),X7)) )),
% 2.70/0.72    inference(superposition,[],[f71,f79])).
% 2.70/0.72  fof(f71,plain,(
% 2.70/0.72    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | r1_tarski(k1_tops_1(X0,X1),X1)) )),
% 2.70/0.72    inference(cnf_transformation,[],[f43])).
% 2.70/0.72  fof(f43,plain,(
% 2.70/0.72    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.70/0.72    inference(ennf_transformation,[],[f20])).
% 2.70/0.72  fof(f20,axiom,(
% 2.70/0.72    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 2.70/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).
% 2.70/0.72  fof(f1382,plain,(
% 2.70/0.72    r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))) | ~r1_tarski(k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)),k3_subset_1(k2_struct_0(sK0),sK1))),
% 2.70/0.72    inference(resolution,[],[f415,f83])).
% 2.70/0.72  fof(f415,plain,(
% 2.70/0.72    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,X0)) | ~r1_tarski(k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)),X0)) )),
% 2.70/0.72    inference(forward_demodulation,[],[f398,f304])).
% 2.70/0.72  fof(f304,plain,(
% 2.70/0.72    k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)))),
% 2.70/0.72    inference(subsumption_resolution,[],[f303,f183])).
% 2.70/0.72  fof(f183,plain,(
% 2.70/0.72    m1_subset_1(k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(k2_struct_0(sK0)))),
% 2.70/0.72    inference(resolution,[],[f146,f57])).
% 2.70/0.72  fof(f146,plain,(
% 2.70/0.72    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0)))),
% 2.70/0.72    inference(resolution,[],[f115,f80])).
% 2.70/0.72  fof(f303,plain,(
% 2.70/0.72    ~m1_subset_1(k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(k2_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)))),
% 2.70/0.72    inference(forward_demodulation,[],[f302,f79])).
% 2.70/0.72  fof(f302,plain,(
% 2.70/0.72    ~m1_subset_1(k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)))),
% 2.70/0.72    inference(subsumption_resolution,[],[f301,f48])).
% 2.70/0.72  fof(f301,plain,(
% 2.70/0.72    ~m1_subset_1(k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1))) | ~l1_pre_topc(sK0)),
% 2.70/0.72    inference(resolution,[],[f172,f50])).
% 2.70/0.72  fof(f50,plain,(
% 2.70/0.72    ( ! [X0,X1] : (~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~l1_pre_topc(X0)) )),
% 2.70/0.72    inference(cnf_transformation,[],[f26])).
% 2.70/0.72  fof(f26,plain,(
% 2.70/0.72    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.70/0.72    inference(ennf_transformation,[],[f17])).
% 2.70/0.72  fof(f17,axiom,(
% 2.70/0.72    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 2.70/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).
% 2.70/0.72  fof(f172,plain,(
% 2.70/0.72    v1_tops_1(k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)),sK0)),
% 2.70/0.72    inference(resolution,[],[f146,f95])).
% 2.70/0.72  fof(f95,plain,(
% 2.70/0.72    ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0))) | v1_tops_1(k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)),sK0)),
% 2.70/0.72    inference(forward_demodulation,[],[f94,f79])).
% 2.70/0.72  fof(f94,plain,(
% 2.70/0.72    ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0))) | v1_tops_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),sK0)),
% 2.70/0.72    inference(forward_demodulation,[],[f93,f79])).
% 2.70/0.72  fof(f93,plain,(
% 2.70/0.72    ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v1_tops_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),sK0)),
% 2.70/0.72    inference(subsumption_resolution,[],[f92,f48])).
% 2.70/0.72  fof(f92,plain,(
% 2.70/0.72    ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v1_tops_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),sK0) | ~l1_pre_topc(sK0)),
% 2.70/0.72    inference(resolution,[],[f78,f52])).
% 2.70/0.72  fof(f52,plain,(
% 2.70/0.72    ( ! [X0,X1] : (~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~l1_pre_topc(X0)) )),
% 2.70/0.72    inference(cnf_transformation,[],[f27])).
% 2.70/0.72  fof(f27,plain,(
% 2.70/0.72    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.70/0.72    inference(ennf_transformation,[],[f18])).
% 2.70/0.72  fof(f18,axiom,(
% 2.70/0.72    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 2.70/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_1)).
% 2.70/0.72  fof(f78,plain,(
% 2.70/0.72    v2_tops_1(k2_pre_topc(sK0,sK1),sK0)),
% 2.70/0.72    inference(subsumption_resolution,[],[f77,f48])).
% 2.70/0.72  fof(f77,plain,(
% 2.70/0.72    v2_tops_1(k2_pre_topc(sK0,sK1),sK0) | ~l1_pre_topc(sK0)),
% 2.70/0.72    inference(subsumption_resolution,[],[f76,f45])).
% 2.70/0.72  fof(f76,plain,(
% 2.70/0.72    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tops_1(k2_pre_topc(sK0,sK1),sK0) | ~l1_pre_topc(sK0)),
% 2.70/0.72    inference(resolution,[],[f46,f59])).
% 2.70/0.72  fof(f59,plain,(
% 2.70/0.72    ( ! [X0,X1] : (~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tops_1(k2_pre_topc(X0,X1),X0) | ~l1_pre_topc(X0)) )),
% 2.70/0.72    inference(cnf_transformation,[],[f33])).
% 2.70/0.72  fof(f33,plain,(
% 2.70/0.72    ! [X0] : (! [X1] : ((v3_tops_1(X1,X0) <=> v2_tops_1(k2_pre_topc(X0,X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.70/0.72    inference(ennf_transformation,[],[f19])).
% 2.70/0.72  fof(f19,axiom,(
% 2.70/0.72    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) <=> v2_tops_1(k2_pre_topc(X0,X1),X0))))),
% 2.70/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tops_1)).
% 2.70/0.72  fof(f46,plain,(
% 2.70/0.72    v3_tops_1(sK1,sK0)),
% 2.70/0.72    inference(cnf_transformation,[],[f25])).
% 2.70/0.72  fof(f398,plain,(
% 2.70/0.72    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1)),X0) | r1_tarski(k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,sK1))),k2_pre_topc(sK0,X0))) )),
% 2.70/0.72    inference(resolution,[],[f183,f116])).
% 2.70/0.72  fof(f116,plain,(
% 2.70/0.72    ( ! [X4,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X3,X4) | r1_tarski(k2_pre_topc(sK0,X3),k2_pre_topc(sK0,X4))) )),
% 2.70/0.72    inference(subsumption_resolution,[],[f109,f48])).
% 2.70/0.72  fof(f109,plain,(
% 2.70/0.72    ( ! [X4,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X3,X4) | r1_tarski(k2_pre_topc(sK0,X3),k2_pre_topc(sK0,X4))) )),
% 2.70/0.72    inference(superposition,[],[f63,f79])).
% 2.70/0.72  fof(f63,plain,(
% 2.70/0.72    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) )),
% 2.70/0.72    inference(cnf_transformation,[],[f37])).
% 2.70/0.72  fof(f37,plain,(
% 2.70/0.72    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.70/0.72    inference(flattening,[],[f36])).
% 2.70/0.72  fof(f36,plain,(
% 2.70/0.72    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.70/0.72    inference(ennf_transformation,[],[f15])).
% 2.70/0.72  fof(f15,axiom,(
% 2.70/0.72    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 2.70/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_pre_topc)).
% 2.70/0.72  fof(f650,plain,(
% 2.70/0.72    k2_struct_0(sK0) != k3_subset_1(k2_struct_0(sK0),k1_tops_1(sK0,sK1))),
% 2.70/0.72    inference(superposition,[],[f153,f227])).
% 2.70/0.72  fof(f153,plain,(
% 2.70/0.72    k2_struct_0(sK0) != k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1))),
% 2.70/0.72    inference(subsumption_resolution,[],[f152,f81])).
% 2.70/0.72  fof(f81,plain,(
% 2.70/0.72    ~v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0)),
% 2.70/0.72    inference(backward_demodulation,[],[f47,f79])).
% 2.70/0.72  fof(f47,plain,(
% 2.70/0.72    ~v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 2.70/0.72    inference(cnf_transformation,[],[f25])).
% 2.70/0.72  fof(f152,plain,(
% 2.70/0.72    k2_struct_0(sK0) != k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)) | v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0)),
% 2.70/0.72    inference(resolution,[],[f113,f83])).
% 2.70/0.72  fof(f113,plain,(
% 2.70/0.72    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_struct_0(sK0) != k2_pre_topc(sK0,X0) | v1_tops_1(X0,sK0)) )),
% 2.70/0.72    inference(subsumption_resolution,[],[f106,f48])).
% 2.70/0.72  fof(f106,plain,(
% 2.70/0.72    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | k2_struct_0(sK0) != k2_pre_topc(sK0,X0) | v1_tops_1(X0,sK0)) )),
% 2.70/0.72    inference(superposition,[],[f49,f79])).
% 2.70/0.72  fof(f49,plain,(
% 2.70/0.72    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1) | v1_tops_1(X1,X0)) )),
% 2.70/0.72    inference(cnf_transformation,[],[f26])).
% 2.70/0.72  fof(f374,plain,(
% 2.70/0.72    ~r1_tarski(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k1_tops_1(sK0,sK1))) | k2_struct_0(sK0) = k3_subset_1(k2_struct_0(sK0),k1_tops_1(sK0,sK1))),
% 2.70/0.72    inference(resolution,[],[f236,f67])).
% 2.70/0.72  fof(f67,plain,(
% 2.70/0.72    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 2.70/0.72    inference(cnf_transformation,[],[f1])).
% 2.70/0.72  fof(f1,axiom,(
% 2.70/0.72    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.70/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.70/0.72  fof(f236,plain,(
% 2.70/0.72    r1_tarski(k3_subset_1(k2_struct_0(sK0),k1_tops_1(sK0,sK1)),k2_struct_0(sK0))),
% 2.70/0.72    inference(backward_demodulation,[],[f214,f227])).
% 2.70/0.72  fof(f214,plain,(
% 2.70/0.72    r1_tarski(k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK1)),k2_struct_0(sK0))),
% 2.70/0.72    inference(resolution,[],[f147,f61])).
% 2.70/0.72  fof(f61,plain,(
% 2.70/0.72    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.70/0.72    inference(cnf_transformation,[],[f10])).
% 2.70/0.72  fof(f10,axiom,(
% 2.70/0.72    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.70/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 2.70/0.72  % SZS output end Proof for theBenchmark
% 2.70/0.72  % (23744)------------------------------
% 2.70/0.72  % (23744)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.70/0.72  % (23744)Termination reason: Refutation
% 2.70/0.72  
% 2.70/0.72  % (23744)Memory used [KB]: 7419
% 2.70/0.72  % (23744)Time elapsed: 0.293 s
% 2.70/0.72  % (23744)------------------------------
% 2.70/0.72  % (23744)------------------------------
% 2.70/0.72  % (23738)Success in time 0.359 s
%------------------------------------------------------------------------------
