%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:39 EST 2020

% Result     : Theorem 1.49s
% Output     : Refutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :  165 (2743 expanded)
%              Number of leaves         :   20 ( 759 expanded)
%              Depth                    :   35
%              Number of atoms          :  417 (8625 expanded)
%              Number of equality atoms :   66 ( 782 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1678,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1677,f101])).

fof(f101,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f60,f99])).

fof(f99,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f96,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f96,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f66,f59])).

fof(f59,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,
    ( ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    & v3_tops_1(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f49,f48])).

fof(f48,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
            & v3_tops_1(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),X1),sK0)
          & v3_tops_1(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X1] :
        ( ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),X1),sK0)
        & v3_tops_1(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
      & v3_tops_1(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_tops_1)).

fof(f66,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f60,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f50])).

fof(f1677,plain,(
    ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f1676,f99])).

fof(f1676,plain,(
    ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f1675,f102])).

fof(f102,plain,(
    ~ v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) ),
    inference(backward_demodulation,[],[f62,f99])).

fof(f62,plain,(
    ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f1675,plain,
    ( v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f1674,f99])).

fof(f1674,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f1672,f59])).

fof(f1672,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f1608,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v2_tops_1(X1,X0)
      | v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_1)).

fof(f1608,plain,(
    v2_tops_1(sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f1524])).

fof(f1524,plain,
    ( k1_xboole_0 != k1_xboole_0
    | v2_tops_1(sK1,sK0) ),
    inference(backward_demodulation,[],[f175,f1522])).

fof(f1522,plain,(
    k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f1520,f555])).

fof(f555,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),k1_xboole_0) ),
    inference(forward_demodulation,[],[f554,f531])).

fof(f531,plain,(
    k1_xboole_0 = k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f135,f172])).

fof(f172,plain,(
    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(resolution,[],[f125,f101])).

fof(f125,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(forward_demodulation,[],[f124,f99])).

fof(f124,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(forward_demodulation,[],[f123,f99])).

fof(f123,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f85,f59])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f135,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | k1_xboole_0 = k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
    inference(forward_demodulation,[],[f134,f99])).

fof(f134,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,k2_pre_topc(sK0,sK1))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f133,f59])).

fof(f133,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,k2_pre_topc(sK0,sK1))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f131,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v2_tops_1(X1,X0)
      | k1_tops_1(X0,X1) = k1_xboole_0
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_tops_1(X0,X1) != k1_xboole_0 )
            & ( k1_tops_1(X0,X1) = k1_xboole_0
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_tops_1(X0,X1) = k1_xboole_0 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_tops_1(X0,X1) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

fof(f131,plain,(
    v2_tops_1(k2_pre_topc(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f130,f101])).

fof(f130,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | v2_tops_1(k2_pre_topc(sK0,sK1),sK0) ),
    inference(forward_demodulation,[],[f129,f99])).

fof(f129,plain,
    ( v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f128,f59])).

fof(f128,plain,
    ( v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f76,f61])).

fof(f61,plain,(
    v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v3_tops_1(X1,X0)
      | v2_tops_1(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tops_1(X1,X0)
              | ~ v2_tops_1(k2_pre_topc(X0,X1),X0) )
            & ( v2_tops_1(k2_pre_topc(X0,X1),X0)
              | ~ v3_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tops_1(X1,X0)
          <=> v2_tops_1(k2_pre_topc(X0,X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
          <=> v2_tops_1(k2_pre_topc(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tops_1)).

fof(f554,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f547,f166])).

fof(f166,plain,(
    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f118,f101])).

fof(f118,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | r1_tarski(X0,k2_pre_topc(sK0,X0)) ) ),
    inference(forward_demodulation,[],[f117,f99])).

fof(f117,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(X0,k2_pre_topc(sK0,X0)) ) ),
    inference(resolution,[],[f67,f59])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

fof(f547,plain,
    ( ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) ),
    inference(resolution,[],[f199,f172])).

fof(f199,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r1_tarski(sK1,X1)
      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,X1)) ) ),
    inference(resolution,[],[f152,f101])).

fof(f152,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r1_tarski(X0,X1)
      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) ) ),
    inference(forward_demodulation,[],[f151,f99])).

fof(f151,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) ) ),
    inference(forward_demodulation,[],[f150,f99])).

fof(f150,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) ) ),
    inference(resolution,[],[f78,f59])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

fof(f1520,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_xboole_0) ),
    inference(resolution,[],[f1414,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1414,plain,(
    r1_tarski(k1_xboole_0,k1_tops_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f1212,f1387])).

fof(f1387,plain,(
    k1_xboole_0 = k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f1386,f209])).

fof(f209,plain,(
    ! [X6] : m1_subset_1(k3_subset_1(X6,X6),k1_zfmisc_1(X6)) ),
    inference(resolution,[],[f104,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f104,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f90,f93])).

fof(f93,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f1386,plain,
    ( ~ m1_subset_1(k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),k1_zfmisc_1(k2_struct_0(sK0)))
    | k1_xboole_0 = k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f1385,f99])).

fof(f1385,plain,
    ( k1_xboole_0 = k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f1384,f1096])).

fof(f1096,plain,(
    k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) = k1_tops_1(sK0,k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f969,f903])).

fof(f903,plain,(
    k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f901,f211])).

fof(f211,plain,(
    r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0))) ),
    inference(resolution,[],[f104,f118])).

fof(f901,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0))
    | ~ r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0))) ),
    inference(resolution,[],[f322,f88])).

fof(f322,plain,(
    r1_tarski(k2_pre_topc(sK0,k2_struct_0(sK0)),k2_struct_0(sK0)) ),
    inference(resolution,[],[f213,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f213,plain,(
    m1_subset_1(k2_pre_topc(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(resolution,[],[f104,f125])).

fof(f969,plain,(
    k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0))) = k1_tops_1(sK0,k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f241,f956])).

fof(f956,plain,(
    k2_struct_0(sK0) = k2_subset_1(k2_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f955,f903])).

fof(f955,plain,(
    k2_subset_1(k2_struct_0(sK0)) = k2_pre_topc(sK0,k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f920,f675])).

fof(f675,plain,(
    ! [X7] : r1_tarski(k3_subset_1(X7,X7),X7) ),
    inference(resolution,[],[f209,f89])).

fof(f920,plain,
    ( ~ r1_tarski(k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),k2_struct_0(sK0))
    | k2_subset_1(k2_struct_0(sK0)) = k2_pre_topc(sK0,k2_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f319,f903])).

fof(f319,plain,
    ( ~ r1_tarski(k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0))),k2_pre_topc(sK0,k2_struct_0(sK0)))
    | k2_subset_1(k2_struct_0(sK0)) = k2_pre_topc(sK0,k2_struct_0(sK0)) ),
    inference(resolution,[],[f213,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r1_tarski(k3_subset_1(X0,X1),X1)
      | k2_subset_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( ( r1_tarski(k3_subset_1(X0,X1),X1)
          | k2_subset_1(X0) != X1 )
        & ( k2_subset_1(X0) = X1
          | ~ r1_tarski(k3_subset_1(X0,X1),X1) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).

fof(f241,plain,(
    k1_tops_1(sK0,k3_subset_1(k2_struct_0(sK0),k2_subset_1(k2_struct_0(sK0)))) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k2_subset_1(k2_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f233,f112])).

fof(f112,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k3_subset_1(X0,k2_subset_1(X0))) ),
    inference(resolution,[],[f80,f63])).

fof(f63,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f233,plain,(
    k1_tops_1(sK0,k3_subset_1(k2_struct_0(sK0),k2_subset_1(k2_struct_0(sK0)))) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_subset_1(k2_struct_0(sK0)))))) ),
    inference(resolution,[],[f110,f149])).

fof(f149,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k1_tops_1(sK0,X0) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) ) ),
    inference(forward_demodulation,[],[f148,f99])).

fof(f148,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) ) ),
    inference(forward_demodulation,[],[f147,f99])).

fof(f147,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) ) ),
    inference(resolution,[],[f69,f59])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

fof(f110,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,k2_subset_1(X0)),k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f79,f63])).

fof(f1384,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f1380,f59])).

fof(f1380,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f1235,f70])).

fof(f1235,plain,(
    v2_tops_1(k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),sK0) ),
    inference(subsumption_resolution,[],[f1234,f947])).

fof(f947,plain,(
    v1_tops_1(k2_struct_0(sK0),sK0) ),
    inference(trivial_inequality_removal,[],[f906])).

fof(f906,plain,
    ( k2_struct_0(sK0) != k2_struct_0(sK0)
    | v1_tops_1(k2_struct_0(sK0),sK0) ),
    inference(backward_demodulation,[],[f215,f903])).

fof(f215,plain,
    ( k2_struct_0(sK0) != k2_pre_topc(sK0,k2_struct_0(sK0))
    | v1_tops_1(k2_struct_0(sK0),sK0) ),
    inference(resolution,[],[f104,f142])).

fof(f142,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k2_struct_0(sK0) != k2_pre_topc(sK0,X0)
      | v1_tops_1(X0,sK0) ) ),
    inference(forward_demodulation,[],[f141,f99])).

fof(f141,plain,(
    ! [X0] :
      ( k2_struct_0(sK0) != k2_pre_topc(sK0,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_tops_1(X0,sK0) ) ),
    inference(resolution,[],[f75,f59])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | k2_struct_0(X0) != k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

fof(f1234,plain,
    ( ~ v1_tops_1(k2_struct_0(sK0),sK0)
    | v2_tops_1(k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),sK0) ),
    inference(forward_demodulation,[],[f1076,f956])).

fof(f1076,plain,
    ( v2_tops_1(k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),sK0)
    | ~ v1_tops_1(k2_subset_1(k2_struct_0(sK0)),sK0) ),
    inference(backward_demodulation,[],[f822,f956])).

fof(f822,plain,
    ( ~ v1_tops_1(k2_subset_1(k2_struct_0(sK0)),sK0)
    | v2_tops_1(k3_subset_1(k2_struct_0(sK0),k2_subset_1(k2_struct_0(sK0))),sK0) ),
    inference(subsumption_resolution,[],[f821,f59])).

fof(f821,plain,
    ( ~ v1_tops_1(k2_subset_1(k2_struct_0(sK0)),sK0)
    | v2_tops_1(k3_subset_1(k2_struct_0(sK0),k2_subset_1(k2_struct_0(sK0))),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f255,f99])).

fof(f255,plain,(
    ! [X0] :
      ( ~ v1_tops_1(k2_subset_1(u1_struct_0(X0)),X0)
      | v2_tops_1(k3_subset_1(u1_struct_0(X0),k2_subset_1(u1_struct_0(X0))),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f254,f110])).

fof(f254,plain,(
    ! [X0] :
      ( ~ v1_tops_1(k2_subset_1(u1_struct_0(X0)),X0)
      | v2_tops_1(k3_subset_1(u1_struct_0(X0),k2_subset_1(u1_struct_0(X0))),X0)
      | ~ m1_subset_1(k3_subset_1(u1_struct_0(X0),k2_subset_1(u1_struct_0(X0))),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f73,f112])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f1212,plain,(
    r1_tarski(k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),k1_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1211,f903])).

fof(f1211,plain,(
    r1_tarski(k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0))),k1_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1210,f956])).

fof(f1210,plain,(
    r1_tarski(k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k2_subset_1(k2_struct_0(sK0)))),k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1059,f797])).

fof(f797,plain,(
    r1_tarski(k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),sK1) ),
    inference(subsumption_resolution,[],[f783,f160])).

fof(f160,plain,(
    r1_tarski(k3_subset_1(k2_struct_0(sK0),sK1),k2_struct_0(sK0)) ),
    inference(resolution,[],[f111,f89])).

fof(f111,plain,(
    m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(resolution,[],[f79,f101])).

fof(f783,plain,
    ( r1_tarski(k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),sK1)
    | ~ r1_tarski(k3_subset_1(k2_struct_0(sK0),sK1),k2_struct_0(sK0)) ),
    inference(resolution,[],[f205,f101])).

fof(f205,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r1_tarski(k3_subset_1(X0,X0),X1)
      | ~ r1_tarski(k3_subset_1(X0,X1),X0) ) ),
    inference(resolution,[],[f104,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ r1_tarski(k3_subset_1(X0,X1),X2)
      | r1_tarski(k3_subset_1(X0,X2),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k3_subset_1(X0,X2),X1)
          | ~ r1_tarski(k3_subset_1(X0,X1),X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k3_subset_1(X0,X2),X1)
          | ~ r1_tarski(k3_subset_1(X0,X1),X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(k3_subset_1(X0,X1),X2)
           => r1_tarski(k3_subset_1(X0,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_subset_1)).

fof(f1059,plain,
    ( ~ r1_tarski(k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),sK1)
    | r1_tarski(k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k2_subset_1(k2_struct_0(sK0)))),k1_tops_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f660,f956])).

fof(f660,plain,
    ( r1_tarski(k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k2_subset_1(k2_struct_0(sK0)))),k1_tops_1(sK0,sK1))
    | ~ r1_tarski(k3_subset_1(k2_struct_0(sK0),k2_subset_1(k2_struct_0(sK0))),sK1) ),
    inference(resolution,[],[f244,f101])).

fof(f244,plain,(
    ! [X8] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_struct_0(sK0)))
      | r1_tarski(k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k2_subset_1(k2_struct_0(sK0)))),k1_tops_1(sK0,X8))
      | ~ r1_tarski(k3_subset_1(k2_struct_0(sK0),k2_subset_1(k2_struct_0(sK0))),X8) ) ),
    inference(forward_demodulation,[],[f234,f241])).

fof(f234,plain,(
    ! [X8] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r1_tarski(k3_subset_1(k2_struct_0(sK0),k2_subset_1(k2_struct_0(sK0))),X8)
      | r1_tarski(k1_tops_1(sK0,k3_subset_1(k2_struct_0(sK0),k2_subset_1(k2_struct_0(sK0)))),k1_tops_1(sK0,X8)) ) ),
    inference(resolution,[],[f110,f152])).

fof(f175,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0) ),
    inference(resolution,[],[f127,f101])).

fof(f127,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k1_xboole_0 != k1_tops_1(sK0,X0)
      | v2_tops_1(X0,sK0) ) ),
    inference(forward_demodulation,[],[f126,f99])).

fof(f126,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_tops_1(sK0,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_tops_1(X0,sK0) ) ),
    inference(resolution,[],[f71,f59])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | k1_tops_1(X0,X1) != k1_xboole_0
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f51])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:47:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (32349)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.50  % (32341)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.50  % (32330)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.50  % (32332)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.50  % (32328)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.51  % (32355)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (32347)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.52  % (32339)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.52  % (32340)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.52  % (32329)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.52  % (32327)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.52  % (32336)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.53  % (32325)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.53  % (32351)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.34/0.53  % (32326)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.34/0.53  % (32354)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.34/0.53  % (32345)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.34/0.53  % (32348)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.34/0.53  % (32353)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.34/0.53  % (32350)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.34/0.54  % (32352)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.34/0.54  % (32343)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.34/0.54  % (32342)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.34/0.54  % (32344)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.34/0.54  % (32331)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.34/0.54  % (32346)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.34/0.54  % (32334)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.34/0.54  % (32335)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.34/0.55  % (32337)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.49/0.55  % (32333)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.49/0.61  % (32332)Refutation found. Thanks to Tanya!
% 1.49/0.61  % SZS status Theorem for theBenchmark
% 1.49/0.61  % SZS output start Proof for theBenchmark
% 1.49/0.61  fof(f1678,plain,(
% 1.49/0.61    $false),
% 1.49/0.61    inference(subsumption_resolution,[],[f1677,f101])).
% 1.49/0.61  fof(f101,plain,(
% 1.49/0.61    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.49/0.61    inference(backward_demodulation,[],[f60,f99])).
% 1.49/0.61  fof(f99,plain,(
% 1.49/0.61    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 1.49/0.61    inference(resolution,[],[f96,f65])).
% 1.49/0.61  fof(f65,plain,(
% 1.49/0.61    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.49/0.61    inference(cnf_transformation,[],[f26])).
% 1.49/0.61  fof(f26,plain,(
% 1.49/0.61    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.49/0.61    inference(ennf_transformation,[],[f11])).
% 1.49/0.61  fof(f11,axiom,(
% 1.49/0.61    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.49/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 1.49/0.61  fof(f96,plain,(
% 1.49/0.61    l1_struct_0(sK0)),
% 1.49/0.61    inference(resolution,[],[f66,f59])).
% 1.49/0.61  fof(f59,plain,(
% 1.49/0.61    l1_pre_topc(sK0)),
% 1.49/0.61    inference(cnf_transformation,[],[f50])).
% 1.49/0.61  fof(f50,plain,(
% 1.49/0.61    (~v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) & v3_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 1.49/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f49,f48])).
% 1.49/0.61  fof(f48,plain,(
% 1.49/0.61    ? [X0] : (? [X1] : (~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) & v3_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (~v1_tops_1(k3_subset_1(u1_struct_0(sK0),X1),sK0) & v3_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 1.49/0.61    introduced(choice_axiom,[])).
% 1.49/0.61  fof(f49,plain,(
% 1.49/0.61    ? [X1] : (~v1_tops_1(k3_subset_1(u1_struct_0(sK0),X1),sK0) & v3_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (~v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) & v3_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.49/0.61    introduced(choice_axiom,[])).
% 1.49/0.61  fof(f25,plain,(
% 1.49/0.61    ? [X0] : (? [X1] : (~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) & v3_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.49/0.61    inference(flattening,[],[f24])).
% 1.49/0.61  fof(f24,plain,(
% 1.49/0.61    ? [X0] : (? [X1] : ((~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) & v3_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.49/0.61    inference(ennf_transformation,[],[f23])).
% 1.49/0.61  fof(f23,negated_conjecture,(
% 1.49/0.61    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 1.49/0.61    inference(negated_conjecture,[],[f22])).
% 1.49/0.61  fof(f22,conjecture,(
% 1.49/0.61    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 1.49/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_tops_1)).
% 1.49/0.61  fof(f66,plain,(
% 1.49/0.61    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 1.49/0.61    inference(cnf_transformation,[],[f27])).
% 1.49/0.61  fof(f27,plain,(
% 1.49/0.61    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.49/0.61    inference(ennf_transformation,[],[f13])).
% 1.49/0.61  fof(f13,axiom,(
% 1.49/0.61    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.49/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.49/0.62  fof(f60,plain,(
% 1.49/0.62    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.49/0.62    inference(cnf_transformation,[],[f50])).
% 1.49/0.62  fof(f1677,plain,(
% 1.49/0.62    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.49/0.62    inference(forward_demodulation,[],[f1676,f99])).
% 1.49/0.62  fof(f1676,plain,(
% 1.49/0.62    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.49/0.62    inference(subsumption_resolution,[],[f1675,f102])).
% 1.49/0.62  fof(f102,plain,(
% 1.49/0.62    ~v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0)),
% 1.49/0.62    inference(backward_demodulation,[],[f62,f99])).
% 1.49/0.62  fof(f62,plain,(
% 1.49/0.62    ~v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 1.49/0.62    inference(cnf_transformation,[],[f50])).
% 1.49/0.62  fof(f1675,plain,(
% 1.49/0.62    v1_tops_1(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.49/0.62    inference(forward_demodulation,[],[f1674,f99])).
% 1.49/0.62  fof(f1674,plain,(
% 1.49/0.62    v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.49/0.62    inference(subsumption_resolution,[],[f1672,f59])).
% 1.49/0.62  fof(f1672,plain,(
% 1.49/0.62    v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.49/0.62    inference(resolution,[],[f1608,f72])).
% 1.49/0.62  fof(f72,plain,(
% 1.49/0.62    ( ! [X0,X1] : (~v2_tops_1(X1,X0) | v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.49/0.62    inference(cnf_transformation,[],[f52])).
% 1.49/0.62  fof(f52,plain,(
% 1.49/0.62    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.49/0.62    inference(nnf_transformation,[],[f32])).
% 1.49/0.62  fof(f32,plain,(
% 1.49/0.62    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.49/0.62    inference(ennf_transformation,[],[f17])).
% 1.49/0.62  fof(f17,axiom,(
% 1.49/0.62    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 1.49/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_1)).
% 1.49/0.62  fof(f1608,plain,(
% 1.49/0.62    v2_tops_1(sK1,sK0)),
% 1.49/0.62    inference(trivial_inequality_removal,[],[f1524])).
% 1.49/0.62  fof(f1524,plain,(
% 1.49/0.62    k1_xboole_0 != k1_xboole_0 | v2_tops_1(sK1,sK0)),
% 1.49/0.62    inference(backward_demodulation,[],[f175,f1522])).
% 1.49/0.62  fof(f1522,plain,(
% 1.49/0.62    k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 1.49/0.62    inference(subsumption_resolution,[],[f1520,f555])).
% 1.49/0.62  fof(f555,plain,(
% 1.49/0.62    r1_tarski(k1_tops_1(sK0,sK1),k1_xboole_0)),
% 1.49/0.62    inference(forward_demodulation,[],[f554,f531])).
% 1.49/0.62  fof(f531,plain,(
% 1.49/0.62    k1_xboole_0 = k1_tops_1(sK0,k2_pre_topc(sK0,sK1))),
% 1.49/0.62    inference(resolution,[],[f135,f172])).
% 1.49/0.62  fof(f172,plain,(
% 1.49/0.62    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.49/0.62    inference(resolution,[],[f125,f101])).
% 1.49/0.62  fof(f125,plain,(
% 1.49/0.62    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 1.49/0.62    inference(forward_demodulation,[],[f124,f99])).
% 1.49/0.62  fof(f124,plain,(
% 1.49/0.62    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.49/0.62    inference(forward_demodulation,[],[f123,f99])).
% 1.49/0.62  fof(f123,plain,(
% 1.49/0.62    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.49/0.62    inference(resolution,[],[f85,f59])).
% 1.49/0.62  fof(f85,plain,(
% 1.49/0.62    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.49/0.62    inference(cnf_transformation,[],[f45])).
% 1.49/0.62  fof(f45,plain,(
% 1.49/0.62    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.49/0.62    inference(flattening,[],[f44])).
% 1.49/0.62  fof(f44,plain,(
% 1.49/0.62    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.49/0.62    inference(ennf_transformation,[],[f12])).
% 1.49/0.62  fof(f12,axiom,(
% 1.49/0.62    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.49/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 1.49/0.62  fof(f135,plain,(
% 1.49/0.62    ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(k2_struct_0(sK0))) | k1_xboole_0 = k1_tops_1(sK0,k2_pre_topc(sK0,sK1))),
% 1.49/0.62    inference(forward_demodulation,[],[f134,f99])).
% 1.49/0.62  fof(f134,plain,(
% 1.49/0.62    k1_xboole_0 = k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.49/0.62    inference(subsumption_resolution,[],[f133,f59])).
% 1.49/0.62  fof(f133,plain,(
% 1.49/0.62    k1_xboole_0 = k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.49/0.62    inference(resolution,[],[f131,f70])).
% 1.49/0.62  fof(f70,plain,(
% 1.49/0.62    ( ! [X0,X1] : (~v2_tops_1(X1,X0) | k1_tops_1(X0,X1) = k1_xboole_0 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.49/0.62    inference(cnf_transformation,[],[f51])).
% 1.49/0.62  fof(f51,plain,(
% 1.49/0.62    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_tops_1(X0,X1) != k1_xboole_0) & (k1_tops_1(X0,X1) = k1_xboole_0 | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.49/0.62    inference(nnf_transformation,[],[f31])).
% 1.49/0.62  fof(f31,plain,(
% 1.49/0.62    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_tops_1(X0,X1) = k1_xboole_0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.49/0.62    inference(ennf_transformation,[],[f21])).
% 1.49/0.62  fof(f21,axiom,(
% 1.49/0.62    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_tops_1(X0,X1) = k1_xboole_0)))),
% 1.49/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).
% 1.49/0.62  fof(f131,plain,(
% 1.49/0.62    v2_tops_1(k2_pre_topc(sK0,sK1),sK0)),
% 1.49/0.62    inference(subsumption_resolution,[],[f130,f101])).
% 1.49/0.62  fof(f130,plain,(
% 1.49/0.62    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | v2_tops_1(k2_pre_topc(sK0,sK1),sK0)),
% 1.49/0.62    inference(forward_demodulation,[],[f129,f99])).
% 1.49/0.62  fof(f129,plain,(
% 1.49/0.62    v2_tops_1(k2_pre_topc(sK0,sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.49/0.62    inference(subsumption_resolution,[],[f128,f59])).
% 1.49/0.62  fof(f128,plain,(
% 1.49/0.62    v2_tops_1(k2_pre_topc(sK0,sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.49/0.62    inference(resolution,[],[f76,f61])).
% 1.49/0.62  fof(f61,plain,(
% 1.49/0.62    v3_tops_1(sK1,sK0)),
% 1.49/0.62    inference(cnf_transformation,[],[f50])).
% 1.49/0.62  fof(f76,plain,(
% 1.49/0.62    ( ! [X0,X1] : (~v3_tops_1(X1,X0) | v2_tops_1(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.49/0.62    inference(cnf_transformation,[],[f54])).
% 1.49/0.62  fof(f54,plain,(
% 1.49/0.62    ! [X0] : (! [X1] : (((v3_tops_1(X1,X0) | ~v2_tops_1(k2_pre_topc(X0,X1),X0)) & (v2_tops_1(k2_pre_topc(X0,X1),X0) | ~v3_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.49/0.62    inference(nnf_transformation,[],[f34])).
% 1.49/0.62  fof(f34,plain,(
% 1.49/0.62    ! [X0] : (! [X1] : ((v3_tops_1(X1,X0) <=> v2_tops_1(k2_pre_topc(X0,X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.49/0.62    inference(ennf_transformation,[],[f18])).
% 1.49/0.62  fof(f18,axiom,(
% 1.49/0.62    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) <=> v2_tops_1(k2_pre_topc(X0,X1),X0))))),
% 1.49/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tops_1)).
% 1.49/0.62  fof(f554,plain,(
% 1.49/0.62    r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))),
% 1.49/0.62    inference(subsumption_resolution,[],[f547,f166])).
% 1.49/0.62  fof(f166,plain,(
% 1.49/0.62    r1_tarski(sK1,k2_pre_topc(sK0,sK1))),
% 1.49/0.62    inference(resolution,[],[f118,f101])).
% 1.49/0.62  fof(f118,plain,(
% 1.49/0.62    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | r1_tarski(X0,k2_pre_topc(sK0,X0))) )),
% 1.49/0.62    inference(forward_demodulation,[],[f117,f99])).
% 1.49/0.62  fof(f117,plain,(
% 1.49/0.62    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X0,k2_pre_topc(sK0,X0))) )),
% 1.49/0.62    inference(resolution,[],[f67,f59])).
% 1.49/0.62  fof(f67,plain,(
% 1.49/0.62    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(X1,k2_pre_topc(X0,X1))) )),
% 1.49/0.62    inference(cnf_transformation,[],[f28])).
% 1.49/0.62  fof(f28,plain,(
% 1.49/0.62    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.49/0.62    inference(ennf_transformation,[],[f14])).
% 1.49/0.62  fof(f14,axiom,(
% 1.49/0.62    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 1.49/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).
% 1.49/0.62  fof(f547,plain,(
% 1.49/0.62    ~r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))),
% 1.49/0.62    inference(resolution,[],[f199,f172])).
% 1.49/0.62  fof(f199,plain,(
% 1.49/0.62    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(sK1,X1) | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,X1))) )),
% 1.49/0.62    inference(resolution,[],[f152,f101])).
% 1.49/0.62  fof(f152,plain,(
% 1.49/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X0,X1) | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1))) )),
% 1.49/0.62    inference(forward_demodulation,[],[f151,f99])).
% 1.49/0.62  fof(f151,plain,(
% 1.49/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1))) )),
% 1.49/0.62    inference(forward_demodulation,[],[f150,f99])).
% 1.49/0.62  fof(f150,plain,(
% 1.49/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1))) )),
% 1.49/0.62    inference(resolution,[],[f78,f59])).
% 1.49/0.62  fof(f78,plain,(
% 1.49/0.62    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))) )),
% 1.49/0.62    inference(cnf_transformation,[],[f36])).
% 1.49/0.62  fof(f36,plain,(
% 1.49/0.62    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.49/0.62    inference(flattening,[],[f35])).
% 1.49/0.62  fof(f35,plain,(
% 1.49/0.62    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.49/0.62    inference(ennf_transformation,[],[f20])).
% 1.49/0.62  fof(f20,axiom,(
% 1.49/0.62    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 1.49/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).
% 1.49/0.62  fof(f1520,plain,(
% 1.49/0.62    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~r1_tarski(k1_tops_1(sK0,sK1),k1_xboole_0)),
% 1.49/0.62    inference(resolution,[],[f1414,f88])).
% 1.49/0.62  fof(f88,plain,(
% 1.49/0.62    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.49/0.62    inference(cnf_transformation,[],[f57])).
% 1.49/0.62  fof(f57,plain,(
% 1.49/0.62    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.49/0.62    inference(flattening,[],[f56])).
% 1.49/0.62  fof(f56,plain,(
% 1.49/0.62    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.49/0.62    inference(nnf_transformation,[],[f1])).
% 1.49/0.62  fof(f1,axiom,(
% 1.49/0.62    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.49/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.49/0.62  fof(f1414,plain,(
% 1.49/0.62    r1_tarski(k1_xboole_0,k1_tops_1(sK0,sK1))),
% 1.49/0.62    inference(backward_demodulation,[],[f1212,f1387])).
% 1.49/0.62  fof(f1387,plain,(
% 1.49/0.62    k1_xboole_0 = k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0))),
% 1.49/0.62    inference(subsumption_resolution,[],[f1386,f209])).
% 1.49/0.62  fof(f209,plain,(
% 1.49/0.62    ( ! [X6] : (m1_subset_1(k3_subset_1(X6,X6),k1_zfmisc_1(X6))) )),
% 1.49/0.62    inference(resolution,[],[f104,f79])).
% 1.49/0.62  fof(f79,plain,(
% 1.49/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 1.49/0.62    inference(cnf_transformation,[],[f37])).
% 1.49/0.62  fof(f37,plain,(
% 1.49/0.62    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.49/0.62    inference(ennf_transformation,[],[f4])).
% 1.49/0.62  fof(f4,axiom,(
% 1.49/0.62    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.49/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 1.49/0.62  fof(f104,plain,(
% 1.49/0.62    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.49/0.62    inference(resolution,[],[f90,f93])).
% 1.49/0.62  fof(f93,plain,(
% 1.49/0.62    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.49/0.62    inference(equality_resolution,[],[f87])).
% 1.49/0.62  fof(f87,plain,(
% 1.49/0.62    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.49/0.62    inference(cnf_transformation,[],[f57])).
% 1.49/0.62  fof(f90,plain,(
% 1.49/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.49/0.62    inference(cnf_transformation,[],[f58])).
% 1.49/0.62  fof(f58,plain,(
% 1.49/0.62    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.49/0.62    inference(nnf_transformation,[],[f10])).
% 1.49/0.62  fof(f10,axiom,(
% 1.49/0.62    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.49/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.49/0.62  fof(f1386,plain,(
% 1.49/0.62    ~m1_subset_1(k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),k1_zfmisc_1(k2_struct_0(sK0))) | k1_xboole_0 = k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0))),
% 1.49/0.62    inference(forward_demodulation,[],[f1385,f99])).
% 1.49/0.62  fof(f1385,plain,(
% 1.49/0.62    k1_xboole_0 = k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.49/0.62    inference(forward_demodulation,[],[f1384,f1096])).
% 1.49/0.62  fof(f1096,plain,(
% 1.49/0.62    k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) = k1_tops_1(sK0,k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)))),
% 1.49/0.62    inference(forward_demodulation,[],[f969,f903])).
% 1.49/0.62  fof(f903,plain,(
% 1.49/0.62    k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0))),
% 1.49/0.62    inference(subsumption_resolution,[],[f901,f211])).
% 1.49/0.62  fof(f211,plain,(
% 1.49/0.62    r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0)))),
% 1.49/0.62    inference(resolution,[],[f104,f118])).
% 1.49/0.62  fof(f901,plain,(
% 1.49/0.62    k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0)) | ~r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0)))),
% 1.49/0.62    inference(resolution,[],[f322,f88])).
% 1.49/0.62  fof(f322,plain,(
% 1.49/0.62    r1_tarski(k2_pre_topc(sK0,k2_struct_0(sK0)),k2_struct_0(sK0))),
% 1.49/0.62    inference(resolution,[],[f213,f89])).
% 1.49/0.62  fof(f89,plain,(
% 1.49/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.49/0.62    inference(cnf_transformation,[],[f58])).
% 1.49/0.62  fof(f213,plain,(
% 1.49/0.62    m1_subset_1(k2_pre_topc(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.49/0.62    inference(resolution,[],[f104,f125])).
% 1.49/0.62  fof(f969,plain,(
% 1.49/0.62    k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0))) = k1_tops_1(sK0,k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)))),
% 1.49/0.62    inference(backward_demodulation,[],[f241,f956])).
% 1.49/0.62  fof(f956,plain,(
% 1.49/0.62    k2_struct_0(sK0) = k2_subset_1(k2_struct_0(sK0))),
% 1.49/0.62    inference(forward_demodulation,[],[f955,f903])).
% 1.49/0.62  fof(f955,plain,(
% 1.49/0.62    k2_subset_1(k2_struct_0(sK0)) = k2_pre_topc(sK0,k2_struct_0(sK0))),
% 1.49/0.62    inference(subsumption_resolution,[],[f920,f675])).
% 1.49/0.62  fof(f675,plain,(
% 1.49/0.62    ( ! [X7] : (r1_tarski(k3_subset_1(X7,X7),X7)) )),
% 1.49/0.62    inference(resolution,[],[f209,f89])).
% 1.49/0.62  fof(f920,plain,(
% 1.49/0.62    ~r1_tarski(k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),k2_struct_0(sK0)) | k2_subset_1(k2_struct_0(sK0)) = k2_pre_topc(sK0,k2_struct_0(sK0))),
% 1.49/0.62    inference(backward_demodulation,[],[f319,f903])).
% 1.49/0.62  fof(f319,plain,(
% 1.49/0.62    ~r1_tarski(k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0))),k2_pre_topc(sK0,k2_struct_0(sK0))) | k2_subset_1(k2_struct_0(sK0)) = k2_pre_topc(sK0,k2_struct_0(sK0))),
% 1.49/0.62    inference(resolution,[],[f213,f81])).
% 1.49/0.62  fof(f81,plain,(
% 1.49/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r1_tarski(k3_subset_1(X0,X1),X1) | k2_subset_1(X0) = X1) )),
% 1.49/0.62    inference(cnf_transformation,[],[f55])).
% 1.49/0.62  fof(f55,plain,(
% 1.49/0.62    ! [X0,X1] : (((r1_tarski(k3_subset_1(X0,X1),X1) | k2_subset_1(X0) != X1) & (k2_subset_1(X0) = X1 | ~r1_tarski(k3_subset_1(X0,X1),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.49/0.62    inference(nnf_transformation,[],[f39])).
% 1.49/0.62  fof(f39,plain,(
% 1.49/0.62    ! [X0,X1] : ((r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.49/0.62    inference(ennf_transformation,[],[f9])).
% 1.49/0.62  fof(f9,axiom,(
% 1.49/0.62    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 1.49/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).
% 1.49/0.62  fof(f241,plain,(
% 1.49/0.62    k1_tops_1(sK0,k3_subset_1(k2_struct_0(sK0),k2_subset_1(k2_struct_0(sK0)))) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k2_subset_1(k2_struct_0(sK0))))),
% 1.49/0.62    inference(forward_demodulation,[],[f233,f112])).
% 1.49/0.62  fof(f112,plain,(
% 1.49/0.62    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k3_subset_1(X0,k2_subset_1(X0)))) )),
% 1.49/0.62    inference(resolution,[],[f80,f63])).
% 1.49/0.62  fof(f63,plain,(
% 1.49/0.62    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.49/0.62    inference(cnf_transformation,[],[f3])).
% 1.49/0.62  fof(f3,axiom,(
% 1.49/0.62    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.49/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.49/0.62  fof(f80,plain,(
% 1.49/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 1.49/0.62    inference(cnf_transformation,[],[f38])).
% 1.49/0.62  fof(f38,plain,(
% 1.49/0.62    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.49/0.62    inference(ennf_transformation,[],[f5])).
% 1.49/0.62  fof(f5,axiom,(
% 1.49/0.62    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 1.49/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 1.49/0.62  fof(f233,plain,(
% 1.49/0.62    k1_tops_1(sK0,k3_subset_1(k2_struct_0(sK0),k2_subset_1(k2_struct_0(sK0)))) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_subset_1(k2_struct_0(sK0))))))),
% 1.49/0.62    inference(resolution,[],[f110,f149])).
% 1.49/0.62  fof(f149,plain,(
% 1.49/0.62    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k1_tops_1(sK0,X0) = k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0)))) )),
% 1.49/0.62    inference(forward_demodulation,[],[f148,f99])).
% 1.49/0.62  fof(f148,plain,(
% 1.49/0.62    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)))) )),
% 1.49/0.62    inference(forward_demodulation,[],[f147,f99])).
% 1.49/0.62  fof(f147,plain,(
% 1.49/0.62    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)))) )),
% 1.49/0.62    inference(resolution,[],[f69,f59])).
% 1.49/0.62  fof(f69,plain,(
% 1.49/0.62    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))) )),
% 1.49/0.62    inference(cnf_transformation,[],[f30])).
% 1.49/0.62  fof(f30,plain,(
% 1.49/0.62    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.49/0.62    inference(ennf_transformation,[],[f15])).
% 1.49/0.62  fof(f15,axiom,(
% 1.49/0.62    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 1.49/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).
% 1.49/0.62  fof(f110,plain,(
% 1.49/0.62    ( ! [X0] : (m1_subset_1(k3_subset_1(X0,k2_subset_1(X0)),k1_zfmisc_1(X0))) )),
% 1.49/0.62    inference(resolution,[],[f79,f63])).
% 1.49/0.62  fof(f1384,plain,(
% 1.49/0.62    k1_xboole_0 = k1_tops_1(sK0,k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0))) | ~m1_subset_1(k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.49/0.62    inference(subsumption_resolution,[],[f1380,f59])).
% 1.49/0.62  fof(f1380,plain,(
% 1.49/0.62    k1_xboole_0 = k1_tops_1(sK0,k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0))) | ~m1_subset_1(k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.49/0.62    inference(resolution,[],[f1235,f70])).
% 1.49/0.62  fof(f1235,plain,(
% 1.49/0.62    v2_tops_1(k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),sK0)),
% 1.49/0.62    inference(subsumption_resolution,[],[f1234,f947])).
% 1.49/0.62  fof(f947,plain,(
% 1.49/0.62    v1_tops_1(k2_struct_0(sK0),sK0)),
% 1.49/0.62    inference(trivial_inequality_removal,[],[f906])).
% 1.49/0.62  fof(f906,plain,(
% 1.49/0.62    k2_struct_0(sK0) != k2_struct_0(sK0) | v1_tops_1(k2_struct_0(sK0),sK0)),
% 1.49/0.62    inference(backward_demodulation,[],[f215,f903])).
% 1.49/0.62  fof(f215,plain,(
% 1.49/0.62    k2_struct_0(sK0) != k2_pre_topc(sK0,k2_struct_0(sK0)) | v1_tops_1(k2_struct_0(sK0),sK0)),
% 1.49/0.62    inference(resolution,[],[f104,f142])).
% 1.49/0.62  fof(f142,plain,(
% 1.49/0.62    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_struct_0(sK0) != k2_pre_topc(sK0,X0) | v1_tops_1(X0,sK0)) )),
% 1.49/0.62    inference(forward_demodulation,[],[f141,f99])).
% 1.49/0.62  fof(f141,plain,(
% 1.49/0.62    ( ! [X0] : (k2_struct_0(sK0) != k2_pre_topc(sK0,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_tops_1(X0,sK0)) )),
% 1.49/0.62    inference(resolution,[],[f75,f59])).
% 1.49/0.62  fof(f75,plain,(
% 1.49/0.62    ( ! [X0,X1] : (~l1_pre_topc(X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_tops_1(X1,X0)) )),
% 1.49/0.62    inference(cnf_transformation,[],[f53])).
% 1.49/0.62  fof(f53,plain,(
% 1.49/0.62    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1)) & (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.49/0.62    inference(nnf_transformation,[],[f33])).
% 1.49/0.62  fof(f33,plain,(
% 1.49/0.62    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.49/0.62    inference(ennf_transformation,[],[f16])).
% 1.49/0.62  fof(f16,axiom,(
% 1.49/0.62    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 1.49/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).
% 1.49/0.62  fof(f1234,plain,(
% 1.49/0.62    ~v1_tops_1(k2_struct_0(sK0),sK0) | v2_tops_1(k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),sK0)),
% 1.49/0.62    inference(forward_demodulation,[],[f1076,f956])).
% 1.49/0.62  fof(f1076,plain,(
% 1.49/0.62    v2_tops_1(k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),sK0) | ~v1_tops_1(k2_subset_1(k2_struct_0(sK0)),sK0)),
% 1.49/0.62    inference(backward_demodulation,[],[f822,f956])).
% 1.49/0.62  fof(f822,plain,(
% 1.49/0.62    ~v1_tops_1(k2_subset_1(k2_struct_0(sK0)),sK0) | v2_tops_1(k3_subset_1(k2_struct_0(sK0),k2_subset_1(k2_struct_0(sK0))),sK0)),
% 1.49/0.62    inference(subsumption_resolution,[],[f821,f59])).
% 1.49/0.62  fof(f821,plain,(
% 1.49/0.62    ~v1_tops_1(k2_subset_1(k2_struct_0(sK0)),sK0) | v2_tops_1(k3_subset_1(k2_struct_0(sK0),k2_subset_1(k2_struct_0(sK0))),sK0) | ~l1_pre_topc(sK0)),
% 1.49/0.62    inference(superposition,[],[f255,f99])).
% 1.49/0.62  fof(f255,plain,(
% 1.49/0.62    ( ! [X0] : (~v1_tops_1(k2_subset_1(u1_struct_0(X0)),X0) | v2_tops_1(k3_subset_1(u1_struct_0(X0),k2_subset_1(u1_struct_0(X0))),X0) | ~l1_pre_topc(X0)) )),
% 1.49/0.62    inference(subsumption_resolution,[],[f254,f110])).
% 1.49/0.62  fof(f254,plain,(
% 1.49/0.62    ( ! [X0] : (~v1_tops_1(k2_subset_1(u1_struct_0(X0)),X0) | v2_tops_1(k3_subset_1(u1_struct_0(X0),k2_subset_1(u1_struct_0(X0))),X0) | ~m1_subset_1(k3_subset_1(u1_struct_0(X0),k2_subset_1(u1_struct_0(X0))),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.49/0.62    inference(superposition,[],[f73,f112])).
% 1.49/0.62  fof(f73,plain,(
% 1.49/0.62    ( ! [X0,X1] : (~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.49/0.62    inference(cnf_transformation,[],[f52])).
% 1.49/0.62  fof(f1212,plain,(
% 1.49/0.62    r1_tarski(k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),k1_tops_1(sK0,sK1))),
% 1.49/0.62    inference(forward_demodulation,[],[f1211,f903])).
% 1.49/0.62  fof(f1211,plain,(
% 1.49/0.62    r1_tarski(k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0))),k1_tops_1(sK0,sK1))),
% 1.49/0.62    inference(forward_demodulation,[],[f1210,f956])).
% 1.49/0.62  fof(f1210,plain,(
% 1.49/0.62    r1_tarski(k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k2_subset_1(k2_struct_0(sK0)))),k1_tops_1(sK0,sK1))),
% 1.49/0.62    inference(subsumption_resolution,[],[f1059,f797])).
% 1.49/0.62  fof(f797,plain,(
% 1.49/0.62    r1_tarski(k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),sK1)),
% 1.49/0.62    inference(subsumption_resolution,[],[f783,f160])).
% 1.49/0.62  fof(f160,plain,(
% 1.49/0.62    r1_tarski(k3_subset_1(k2_struct_0(sK0),sK1),k2_struct_0(sK0))),
% 1.49/0.62    inference(resolution,[],[f111,f89])).
% 1.49/0.62  fof(f111,plain,(
% 1.49/0.62    m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.49/0.62    inference(resolution,[],[f79,f101])).
% 1.49/0.62  fof(f783,plain,(
% 1.49/0.62    r1_tarski(k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),sK1) | ~r1_tarski(k3_subset_1(k2_struct_0(sK0),sK1),k2_struct_0(sK0))),
% 1.49/0.62    inference(resolution,[],[f205,f101])).
% 1.49/0.62  fof(f205,plain,(
% 1.49/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | r1_tarski(k3_subset_1(X0,X0),X1) | ~r1_tarski(k3_subset_1(X0,X1),X0)) )),
% 1.49/0.62    inference(resolution,[],[f104,f84])).
% 1.49/0.62  fof(f84,plain,(
% 1.49/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~r1_tarski(k3_subset_1(X0,X1),X2) | r1_tarski(k3_subset_1(X0,X2),X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.49/0.62    inference(cnf_transformation,[],[f43])).
% 1.49/0.62  fof(f43,plain,(
% 1.49/0.62    ! [X0,X1] : (! [X2] : (r1_tarski(k3_subset_1(X0,X2),X1) | ~r1_tarski(k3_subset_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.49/0.62    inference(flattening,[],[f42])).
% 1.49/0.62  fof(f42,plain,(
% 1.49/0.62    ! [X0,X1] : (! [X2] : ((r1_tarski(k3_subset_1(X0,X2),X1) | ~r1_tarski(k3_subset_1(X0,X1),X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.49/0.62    inference(ennf_transformation,[],[f8])).
% 1.49/0.62  fof(f8,axiom,(
% 1.49/0.62    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X2) => r1_tarski(k3_subset_1(X0,X2),X1))))),
% 1.49/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_subset_1)).
% 1.49/0.62  fof(f1059,plain,(
% 1.49/0.62    ~r1_tarski(k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)),sK1) | r1_tarski(k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k2_subset_1(k2_struct_0(sK0)))),k1_tops_1(sK0,sK1))),
% 1.49/0.62    inference(backward_demodulation,[],[f660,f956])).
% 1.49/0.62  fof(f660,plain,(
% 1.49/0.62    r1_tarski(k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k2_subset_1(k2_struct_0(sK0)))),k1_tops_1(sK0,sK1)) | ~r1_tarski(k3_subset_1(k2_struct_0(sK0),k2_subset_1(k2_struct_0(sK0))),sK1)),
% 1.49/0.62    inference(resolution,[],[f244,f101])).
% 1.49/0.62  fof(f244,plain,(
% 1.49/0.62    ( ! [X8] : (~m1_subset_1(X8,k1_zfmisc_1(k2_struct_0(sK0))) | r1_tarski(k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k2_subset_1(k2_struct_0(sK0)))),k1_tops_1(sK0,X8)) | ~r1_tarski(k3_subset_1(k2_struct_0(sK0),k2_subset_1(k2_struct_0(sK0))),X8)) )),
% 1.49/0.62    inference(forward_demodulation,[],[f234,f241])).
% 1.49/0.62  fof(f234,plain,(
% 1.49/0.62    ( ! [X8] : (~m1_subset_1(X8,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(k3_subset_1(k2_struct_0(sK0),k2_subset_1(k2_struct_0(sK0))),X8) | r1_tarski(k1_tops_1(sK0,k3_subset_1(k2_struct_0(sK0),k2_subset_1(k2_struct_0(sK0)))),k1_tops_1(sK0,X8))) )),
% 1.49/0.62    inference(resolution,[],[f110,f152])).
% 1.49/0.62  fof(f175,plain,(
% 1.49/0.62    k1_xboole_0 != k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)),
% 1.49/0.62    inference(resolution,[],[f127,f101])).
% 1.49/0.62  fof(f127,plain,(
% 1.49/0.62    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k1_xboole_0 != k1_tops_1(sK0,X0) | v2_tops_1(X0,sK0)) )),
% 1.49/0.62    inference(forward_demodulation,[],[f126,f99])).
% 1.49/0.62  fof(f126,plain,(
% 1.49/0.62    ( ! [X0] : (k1_xboole_0 != k1_tops_1(sK0,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tops_1(X0,sK0)) )),
% 1.49/0.62    inference(resolution,[],[f71,f59])).
% 1.49/0.62  fof(f71,plain,(
% 1.49/0.62    ( ! [X0,X1] : (~l1_pre_topc(X0) | k1_tops_1(X0,X1) != k1_xboole_0 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tops_1(X1,X0)) )),
% 1.49/0.62    inference(cnf_transformation,[],[f51])).
% 1.49/0.62  % SZS output end Proof for theBenchmark
% 1.49/0.62  % (32332)------------------------------
% 1.49/0.62  % (32332)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.62  % (32332)Termination reason: Refutation
% 1.49/0.62  
% 1.49/0.62  % (32332)Memory used [KB]: 2430
% 1.49/0.62  % (32332)Time elapsed: 0.179 s
% 1.49/0.62  % (32332)------------------------------
% 1.49/0.62  % (32332)------------------------------
% 1.49/0.63  % (32324)Success in time 0.269 s
%------------------------------------------------------------------------------
