%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:22 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 348 expanded)
%              Number of leaves         :   13 ( 125 expanded)
%              Depth                    :   18
%              Number of atoms          :  198 (1443 expanded)
%              Number of equality atoms :   37 (  69 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1756,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1755,f92])).

fof(f92,plain,(
    ~ r1_tarski(k2_tops_1(sK0,k2_xboole_0(sK1,sK2)),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK2))) ),
    inference(subsumption_resolution,[],[f91,f31])).

fof(f31,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f27,f26,f25])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k2_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)),k4_subset_1(u1_struct_0(X0),k2_tops_1(X0,X1),k2_tops_1(X0,X2)))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2)),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X1),k2_tops_1(sK0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k2_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2)),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X1),k2_tops_1(sK0,X2)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(k2_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,X2)),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k2_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,X2)),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,X2)))
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ r1_tarski(k2_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK2)))
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)),k4_subset_1(u1_struct_0(X0),k2_tops_1(X0,X1),k2_tops_1(X0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)),k4_subset_1(u1_struct_0(X0),k2_tops_1(X0,X1),k2_tops_1(X0,X2)))
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
               => r1_tarski(k2_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)),k4_subset_1(u1_struct_0(X0),k2_tops_1(X0,X1),k2_tops_1(X0,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k2_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)),k4_subset_1(u1_struct_0(X0),k2_tops_1(X0,X1),k2_tops_1(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_tops_1)).

fof(f91,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,k2_xboole_0(sK1,sK2)),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK2)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f89,f32])).

fof(f32,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f89,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,k2_xboole_0(sK1,sK2)),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK2)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f33,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f33,plain,(
    ~ r1_tarski(k2_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f28])).

fof(f1755,plain,(
    r1_tarski(k2_tops_1(sK0,k2_xboole_0(sK1,sK2)),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK2))) ),
    inference(forward_demodulation,[],[f1754,f301])).

fof(f301,plain,(
    k2_tops_1(sK0,k2_xboole_0(sK1,sK2)) = k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK1,sK2))) ),
    inference(backward_demodulation,[],[f266,f277])).

fof(f277,plain,(
    k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f79,f31])).

fof(f79,plain,(
    ! [X8] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_xboole_0(X8,sK2) = k4_subset_1(u1_struct_0(sK0),X8,sK2) ) ),
    inference(resolution,[],[f32,f42])).

fof(f266,plain,(
    k2_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(backward_demodulation,[],[f264,f250])).

fof(f250,plain,(
    k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k4_xboole_0(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    inference(resolution,[],[f179,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f179,plain,(
    m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f55,f32])).

fof(f55,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,X5),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f31,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f264,plain,(
    k2_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(subsumption_resolution,[],[f248,f30])).

fof(f30,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f248,plain,
    ( k2_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f179,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_1)).

fof(f1754,plain,(
    r1_tarski(k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK1,sK2))),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK2))) ),
    inference(forward_demodulation,[],[f1753,f65])).

fof(f65,plain,(
    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(backward_demodulation,[],[f63,f51])).

fof(f51,plain,(
    k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
    inference(resolution,[],[f31,f37])).

fof(f63,plain,(
    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f49,f30])).

fof(f49,plain,
    ( k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f31,f34])).

fof(f1753,plain,(
    r1_tarski(k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK1,sK2))),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)),k2_tops_1(sK0,sK2))) ),
    inference(subsumption_resolution,[],[f1741,f64])).

fof(f64,plain,(
    m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f50,f51])).

fof(f50,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f31,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f1741,plain,
    ( r1_tarski(k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK1,sK2))),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)),k2_tops_1(sK0,sK2)))
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f411,f116])).

fof(f116,plain,(
    ! [X4] : k7_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),X4) = k4_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK1,X4)) ),
    inference(forward_demodulation,[],[f100,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f100,plain,(
    ! [X4] : k7_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),X4) = k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),X4) ),
    inference(resolution,[],[f64,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f411,plain,(
    ! [X0] :
      ( r1_tarski(k2_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),X0,sK2)),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0),k2_tops_1(sK0,sK2)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(forward_demodulation,[],[f410,f86])).

fof(f86,plain,(
    k2_tops_1(sK0,sK2) = k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK2)) ),
    inference(backward_demodulation,[],[f84,f72])).

fof(f72,plain,(
    k3_subset_1(u1_struct_0(sK0),sK2) = k4_xboole_0(u1_struct_0(sK0),sK2) ),
    inference(resolution,[],[f32,f37])).

fof(f84,plain,(
    k2_tops_1(sK0,sK2) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK2)) ),
    inference(subsumption_resolution,[],[f70,f30])).

fof(f70,plain,
    ( k2_tops_1(sK0,sK2) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK2))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f32,f34])).

fof(f410,plain,(
    ! [X0] :
      ( r1_tarski(k2_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),X0,sK2)),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0),k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK2))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f409,f29])).

fof(f29,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f409,plain,(
    ! [X0] :
      ( r1_tarski(k2_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),X0,sK2)),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0),k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK2))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f408,f30])).

fof(f408,plain,(
    ! [X0] :
      ( r1_tarski(k2_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),X0,sK2)),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0),k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK2))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f407,f85])).

fof(f85,plain,(
    m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f71,f72])).

fof(f71,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f32,f36])).

fof(f407,plain,(
    ! [X0] :
      ( r1_tarski(k2_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),X0,sK2)),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0),k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK2))))
      | ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(duplicate_literal_removal,[],[f406])).

fof(f406,plain,(
    ! [X0] :
      ( r1_tarski(k2_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),X0,sK2)),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0),k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK2))))
      | ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(superposition,[],[f35,f87])).

fof(f87,plain,(
    ! [X3] :
      ( k7_subset_1(u1_struct_0(sK0),X3,sK2) = k9_subset_1(u1_struct_0(sK0),X3,k4_xboole_0(u1_struct_0(sK0),sK2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(forward_demodulation,[],[f74,f72])).

fof(f74,plain,(
    ! [X3] :
      ( k7_subset_1(u1_struct_0(sK0),X3,sK2) = k9_subset_1(u1_struct_0(sK0),X3,k3_subset_1(u1_struct_0(sK0),sK2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f32,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k4_subset_1(u1_struct_0(X0),k2_tops_1(X0,X1),k2_tops_1(X0,X2)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k4_subset_1(u1_struct_0(X0),k2_tops_1(X0,X1),k2_tops_1(X0,X2)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k4_subset_1(u1_struct_0(X0),k2_tops_1(X0,X1),k2_tops_1(X0,X2)))
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
             => r1_tarski(k2_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k4_subset_1(u1_struct_0(X0),k2_tops_1(X0,X1),k2_tops_1(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_tops_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 16:18:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.50  % (21963)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.52  % (21966)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.22/0.53  % (21961)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.53  % (21958)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.53  % (21958)Refutation not found, incomplete strategy% (21958)------------------------------
% 0.22/0.53  % (21958)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (21958)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (21958)Memory used [KB]: 10490
% 0.22/0.53  % (21958)Time elapsed: 0.104 s
% 0.22/0.53  % (21958)------------------------------
% 0.22/0.53  % (21958)------------------------------
% 0.22/0.54  % (21956)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.54  % (21973)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.22/0.54  % (21957)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.55  % (21967)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.22/0.55  % (21975)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.55  % (21971)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.22/0.55  % (21969)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.22/0.56  % (21960)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.57  % (21978)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.22/0.57  % (21964)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.22/0.57  % (21955)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.57  % (21965)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.22/0.57  % (21965)Refutation not found, incomplete strategy% (21965)------------------------------
% 0.22/0.57  % (21965)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (21965)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (21965)Memory used [KB]: 10618
% 0.22/0.57  % (21965)Time elapsed: 0.151 s
% 0.22/0.57  % (21965)------------------------------
% 0.22/0.57  % (21965)------------------------------
% 0.22/0.57  % (21959)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.58  % (21966)Refutation found. Thanks to Tanya!
% 0.22/0.58  % SZS status Theorem for theBenchmark
% 0.22/0.58  % SZS output start Proof for theBenchmark
% 0.22/0.58  fof(f1756,plain,(
% 0.22/0.58    $false),
% 0.22/0.58    inference(subsumption_resolution,[],[f1755,f92])).
% 0.22/0.58  fof(f92,plain,(
% 0.22/0.58    ~r1_tarski(k2_tops_1(sK0,k2_xboole_0(sK1,sK2)),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK2)))),
% 0.22/0.58    inference(subsumption_resolution,[],[f91,f31])).
% 0.22/0.58  fof(f31,plain,(
% 0.22/0.58    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.58    inference(cnf_transformation,[],[f28])).
% 0.22/0.58  fof(f28,plain,(
% 0.22/0.58    ((~r1_tarski(k2_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.22/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f27,f26,f25])).
% 0.22/0.58  fof(f25,plain,(
% 0.22/0.58    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k2_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)),k4_subset_1(u1_struct_0(X0),k2_tops_1(X0,X1),k2_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k2_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2)),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X1),k2_tops_1(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f26,plain,(
% 0.22/0.58    ? [X1] : (? [X2] : (~r1_tarski(k2_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2)),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X1),k2_tops_1(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~r1_tarski(k2_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,X2)),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f27,plain,(
% 0.22/0.58    ? [X2] : (~r1_tarski(k2_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,X2)),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~r1_tarski(k2_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f13,plain,(
% 0.22/0.58    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k2_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)),k4_subset_1(u1_struct_0(X0),k2_tops_1(X0,X1),k2_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.58    inference(flattening,[],[f12])).
% 0.22/0.58  fof(f12,plain,(
% 0.22/0.58    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k2_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)),k4_subset_1(u1_struct_0(X0),k2_tops_1(X0,X1),k2_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.22/0.58    inference(ennf_transformation,[],[f11])).
% 0.22/0.58  fof(f11,negated_conjecture,(
% 0.22/0.58    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)),k4_subset_1(u1_struct_0(X0),k2_tops_1(X0,X1),k2_tops_1(X0,X2))))))),
% 0.22/0.58    inference(negated_conjecture,[],[f10])).
% 0.22/0.58  fof(f10,conjecture,(
% 0.22/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)),k4_subset_1(u1_struct_0(X0),k2_tops_1(X0,X1),k2_tops_1(X0,X2))))))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_tops_1)).
% 0.22/0.58  fof(f91,plain,(
% 0.22/0.58    ~r1_tarski(k2_tops_1(sK0,k2_xboole_0(sK1,sK2)),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK2))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.58    inference(subsumption_resolution,[],[f89,f32])).
% 0.22/0.58  fof(f32,plain,(
% 0.22/0.58    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.58    inference(cnf_transformation,[],[f28])).
% 0.22/0.58  fof(f89,plain,(
% 0.22/0.58    ~r1_tarski(k2_tops_1(sK0,k2_xboole_0(sK1,sK2)),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK2))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.58    inference(superposition,[],[f33,f42])).
% 0.22/0.58  fof(f42,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f24])).
% 0.22/0.58  fof(f24,plain,(
% 0.22/0.58    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.58    inference(flattening,[],[f23])).
% 0.22/0.58  fof(f23,plain,(
% 0.22/0.58    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.22/0.58    inference(ennf_transformation,[],[f5])).
% 0.22/0.58  fof(f5,axiom,(
% 0.22/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.22/0.58  fof(f33,plain,(
% 0.22/0.58    ~r1_tarski(k2_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK2)))),
% 0.22/0.58    inference(cnf_transformation,[],[f28])).
% 0.22/0.58  fof(f1755,plain,(
% 0.22/0.58    r1_tarski(k2_tops_1(sK0,k2_xboole_0(sK1,sK2)),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK2)))),
% 0.22/0.58    inference(forward_demodulation,[],[f1754,f301])).
% 0.22/0.58  fof(f301,plain,(
% 0.22/0.58    k2_tops_1(sK0,k2_xboole_0(sK1,sK2)) = k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK1,sK2)))),
% 0.22/0.58    inference(backward_demodulation,[],[f266,f277])).
% 0.22/0.58  fof(f277,plain,(
% 0.22/0.58    k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2)),
% 0.22/0.58    inference(resolution,[],[f79,f31])).
% 0.22/0.58  fof(f79,plain,(
% 0.22/0.58    ( ! [X8] : (~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0))) | k2_xboole_0(X8,sK2) = k4_subset_1(u1_struct_0(sK0),X8,sK2)) )),
% 0.22/0.58    inference(resolution,[],[f32,f42])).
% 0.22/0.58  fof(f266,plain,(
% 0.22/0.58    k2_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 0.22/0.58    inference(backward_demodulation,[],[f264,f250])).
% 0.22/0.58  fof(f250,plain,(
% 0.22/0.58    k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k4_xboole_0(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,sK2))),
% 0.22/0.58    inference(resolution,[],[f179,f37])).
% 0.22/0.58  fof(f37,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f18])).
% 0.22/0.58  fof(f18,plain,(
% 0.22/0.58    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.58    inference(ennf_transformation,[],[f2])).
% 0.22/0.58  fof(f2,axiom,(
% 0.22/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.22/0.58  fof(f179,plain,(
% 0.22/0.58    m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.58    inference(resolution,[],[f55,f32])).
% 0.22/0.58  fof(f55,plain,(
% 0.22/0.58    ( ! [X5] : (~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,X5),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.22/0.58    inference(resolution,[],[f31,f41])).
% 0.22/0.58  fof(f41,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f22])).
% 0.22/0.58  fof(f22,plain,(
% 0.22/0.58    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.58    inference(flattening,[],[f21])).
% 0.22/0.58  fof(f21,plain,(
% 0.22/0.58    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.22/0.58    inference(ennf_transformation,[],[f4])).
% 0.22/0.58  fof(f4,axiom,(
% 0.22/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 0.22/0.58  fof(f264,plain,(
% 0.22/0.58    k2_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 0.22/0.58    inference(subsumption_resolution,[],[f248,f30])).
% 0.22/0.58  fof(f30,plain,(
% 0.22/0.58    l1_pre_topc(sK0)),
% 0.22/0.58    inference(cnf_transformation,[],[f28])).
% 0.22/0.58  fof(f248,plain,(
% 0.22/0.58    k2_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | ~l1_pre_topc(sK0)),
% 0.22/0.58    inference(resolution,[],[f179,f34])).
% 0.22/0.58  fof(f34,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f14])).
% 0.22/0.58  fof(f14,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.58    inference(ennf_transformation,[],[f8])).
% 0.22/0.58  fof(f8,axiom,(
% 0.22/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_1)).
% 0.22/0.58  fof(f1754,plain,(
% 0.22/0.58    r1_tarski(k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK1,sK2))),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK2)))),
% 0.22/0.58    inference(forward_demodulation,[],[f1753,f65])).
% 0.22/0.58  fof(f65,plain,(
% 0.22/0.58    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))),
% 0.22/0.58    inference(backward_demodulation,[],[f63,f51])).
% 0.22/0.58  fof(f51,plain,(
% 0.22/0.58    k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1)),
% 0.22/0.58    inference(resolution,[],[f31,f37])).
% 0.22/0.58  fof(f63,plain,(
% 0.22/0.58    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),
% 0.22/0.58    inference(subsumption_resolution,[],[f49,f30])).
% 0.22/0.58  fof(f49,plain,(
% 0.22/0.58    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | ~l1_pre_topc(sK0)),
% 0.22/0.58    inference(resolution,[],[f31,f34])).
% 0.22/0.58  fof(f1753,plain,(
% 0.22/0.58    r1_tarski(k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK1,sK2))),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)),k2_tops_1(sK0,sK2)))),
% 0.22/0.58    inference(subsumption_resolution,[],[f1741,f64])).
% 0.22/0.58  fof(f64,plain,(
% 0.22/0.58    m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.58    inference(backward_demodulation,[],[f50,f51])).
% 0.22/0.58  fof(f50,plain,(
% 0.22/0.58    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.58    inference(resolution,[],[f31,f36])).
% 0.22/0.58  fof(f36,plain,(
% 0.22/0.58    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f17])).
% 0.22/0.58  fof(f17,plain,(
% 0.22/0.58    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.58    inference(ennf_transformation,[],[f3])).
% 0.22/0.58  fof(f3,axiom,(
% 0.22/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.22/0.58  fof(f1741,plain,(
% 0.22/0.58    r1_tarski(k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK1,sK2))),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)),k2_tops_1(sK0,sK2))) | ~m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.58    inference(superposition,[],[f411,f116])).
% 0.22/0.58  fof(f116,plain,(
% 0.22/0.58    ( ! [X4] : (k7_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),X4) = k4_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK1,X4))) )),
% 0.22/0.58    inference(forward_demodulation,[],[f100,f39])).
% 0.22/0.58  fof(f39,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f1])).
% 0.22/0.58  fof(f1,axiom,(
% 0.22/0.58    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.22/0.58  fof(f100,plain,(
% 0.22/0.58    ( ! [X4] : (k7_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),X4) = k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),X4)) )),
% 0.22/0.58    inference(resolution,[],[f64,f40])).
% 0.22/0.58  fof(f40,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f20])).
% 0.22/0.58  fof(f20,plain,(
% 0.22/0.58    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.58    inference(ennf_transformation,[],[f6])).
% 0.22/0.58  fof(f6,axiom,(
% 0.22/0.58    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.22/0.58  fof(f411,plain,(
% 0.22/0.58    ( ! [X0] : (r1_tarski(k2_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),X0,sK2)),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0),k2_tops_1(sK0,sK2))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.22/0.58    inference(forward_demodulation,[],[f410,f86])).
% 0.22/0.58  fof(f86,plain,(
% 0.22/0.58    k2_tops_1(sK0,sK2) = k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK2))),
% 0.22/0.58    inference(backward_demodulation,[],[f84,f72])).
% 0.22/0.58  fof(f72,plain,(
% 0.22/0.58    k3_subset_1(u1_struct_0(sK0),sK2) = k4_xboole_0(u1_struct_0(sK0),sK2)),
% 0.22/0.58    inference(resolution,[],[f32,f37])).
% 0.22/0.58  fof(f84,plain,(
% 0.22/0.58    k2_tops_1(sK0,sK2) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK2))),
% 0.22/0.58    inference(subsumption_resolution,[],[f70,f30])).
% 0.22/0.58  fof(f70,plain,(
% 0.22/0.58    k2_tops_1(sK0,sK2) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK2)) | ~l1_pre_topc(sK0)),
% 0.22/0.58    inference(resolution,[],[f32,f34])).
% 0.22/0.58  fof(f410,plain,(
% 0.22/0.58    ( ! [X0] : (r1_tarski(k2_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),X0,sK2)),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0),k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK2)))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f409,f29])).
% 0.22/0.58  fof(f29,plain,(
% 0.22/0.58    v2_pre_topc(sK0)),
% 0.22/0.58    inference(cnf_transformation,[],[f28])).
% 0.22/0.58  fof(f409,plain,(
% 0.22/0.58    ( ! [X0] : (r1_tarski(k2_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),X0,sK2)),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0),k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK2)))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0)) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f408,f30])).
% 0.22/0.58  fof(f408,plain,(
% 0.22/0.58    ( ! [X0] : (r1_tarski(k2_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),X0,sK2)),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0),k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK2)))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f407,f85])).
% 0.22/0.58  fof(f85,plain,(
% 0.22/0.58    m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.58    inference(backward_demodulation,[],[f71,f72])).
% 0.22/0.58  fof(f71,plain,(
% 0.22/0.58    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.58    inference(resolution,[],[f32,f36])).
% 0.22/0.58  fof(f407,plain,(
% 0.22/0.58    ( ! [X0] : (r1_tarski(k2_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),X0,sK2)),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0),k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK2)))) | ~m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.22/0.58    inference(duplicate_literal_removal,[],[f406])).
% 0.22/0.58  fof(f406,plain,(
% 0.22/0.58    ( ! [X0] : (r1_tarski(k2_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),X0,sK2)),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0),k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK2)))) | ~m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.22/0.58    inference(superposition,[],[f35,f87])).
% 0.22/0.58  fof(f87,plain,(
% 0.22/0.58    ( ! [X3] : (k7_subset_1(u1_struct_0(sK0),X3,sK2) = k9_subset_1(u1_struct_0(sK0),X3,k4_xboole_0(u1_struct_0(sK0),sK2)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.22/0.58    inference(forward_demodulation,[],[f74,f72])).
% 0.22/0.58  fof(f74,plain,(
% 0.22/0.58    ( ! [X3] : (k7_subset_1(u1_struct_0(sK0),X3,sK2) = k9_subset_1(u1_struct_0(sK0),X3,k3_subset_1(u1_struct_0(sK0),sK2)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.22/0.58    inference(resolution,[],[f32,f38])).
% 0.22/0.58  fof(f38,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f19])).
% 0.22/0.58  fof(f19,plain,(
% 0.22/0.58    ! [X0,X1] : (! [X2] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.58    inference(ennf_transformation,[],[f7])).
% 0.22/0.58  fof(f7,axiom,(
% 0.22/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).
% 0.22/0.58  fof(f35,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (r1_tarski(k2_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k4_subset_1(u1_struct_0(X0),k2_tops_1(X0,X1),k2_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f16])).
% 0.22/0.58  fof(f16,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k4_subset_1(u1_struct_0(X0),k2_tops_1(X0,X1),k2_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.58    inference(flattening,[],[f15])).
% 0.22/0.58  fof(f15,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k4_subset_1(u1_struct_0(X0),k2_tops_1(X0,X1),k2_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.58    inference(ennf_transformation,[],[f9])).
% 0.22/0.58  fof(f9,axiom,(
% 0.22/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k4_subset_1(u1_struct_0(X0),k2_tops_1(X0,X1),k2_tops_1(X0,X2))))))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_tops_1)).
% 0.22/0.58  % SZS output end Proof for theBenchmark
% 0.22/0.58  % (21966)------------------------------
% 0.22/0.58  % (21966)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (21966)Termination reason: Refutation
% 0.22/0.58  
% 0.22/0.58  % (21966)Memory used [KB]: 3198
% 0.22/0.58  % (21966)Time elapsed: 0.145 s
% 0.22/0.58  % (21966)------------------------------
% 0.22/0.58  % (21966)------------------------------
% 0.22/0.58  % (21970)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.58  % (21954)Success in time 0.217 s
%------------------------------------------------------------------------------
