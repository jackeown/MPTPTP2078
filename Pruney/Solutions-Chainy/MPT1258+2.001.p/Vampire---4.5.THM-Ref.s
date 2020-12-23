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
% DateTime   : Thu Dec  3 13:11:29 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 490 expanded)
%              Number of leaves         :   24 ( 168 expanded)
%              Depth                    :   14
%              Number of atoms          :  254 (1407 expanded)
%              Number of equality atoms :   81 ( 443 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f455,plain,(
    $false ),
    inference(subsumption_resolution,[],[f449,f113])).

fof(f113,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,k2_pre_topc(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f80,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

fof(f80,plain,(
    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f55,f56,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

fof(f56,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,
    ( k1_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f52,f51])).

fof(f51,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( k1_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k2_tops_1(sK0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ? [X1] :
        ( k1_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k2_tops_1(sK0,X1))
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( k1_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

fof(f55,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f449,plain,(
    k1_xboole_0 != k4_xboole_0(sK1,k2_pre_topc(sK0,sK1)) ),
    inference(backward_demodulation,[],[f429,f448])).

fof(f448,plain,(
    k2_pre_topc(sK0,sK1) = k2_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f447,f418])).

fof(f418,plain,(
    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f264,f409])).

fof(f409,plain,(
    k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k4_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) ),
    inference(backward_demodulation,[],[f103,f408])).

fof(f408,plain,(
    k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k4_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f407,f216])).

fof(f216,plain,(
    k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) = k4_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f87,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f87,plain,(
    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f55,f56,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(f407,plain,(
    k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f398,f277])).

fof(f277,plain,(
    m1_subset_1(k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f55,f102,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f102,plain,(
    m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f88,f89])).

fof(f89,plain,(
    k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
    inference(unit_resulting_resolution,[],[f56,f65])).

fof(f88,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f56,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f398,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f66,f104])).

fof(f104,plain,(
    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))) ),
    inference(forward_demodulation,[],[f83,f89])).

fof(f83,plain,(
    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    inference(unit_resulting_resolution,[],[f55,f56,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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

fof(f66,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f103,plain,(
    k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))) ),
    inference(forward_demodulation,[],[f84,f89])).

fof(f84,plain,(
    k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    inference(unit_resulting_resolution,[],[f55,f56,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_1)).

fof(f264,plain,(
    k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k4_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) ),
    inference(backward_demodulation,[],[f254,f216])).

fof(f254,plain,(
    k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f222,f173])).

fof(f173,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0) = k4_xboole_0(k2_pre_topc(sK0,sK1),X0) ),
    inference(unit_resulting_resolution,[],[f86,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f86,plain,(
    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f55,f56,f70])).

fof(f222,plain,(
    k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f86,f87,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).

fof(f447,plain,(
    k2_pre_topc(sK0,sK1) = k2_xboole_0(k1_tops_1(sK0,sK1),k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f115,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

fof(f115,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f80,f81,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f81,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f55,f56,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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

fof(f429,plain,(
    k1_xboole_0 != k4_xboole_0(sK1,k2_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f426,f118])).

fof(f118,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),k4_xboole_0(sK1,k2_tops_1(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f81,f82,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

fof(f82,plain,(
    r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f55,f56,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_tops_1)).

fof(f426,plain,
    ( k1_xboole_0 != k4_xboole_0(sK1,k2_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),k4_xboole_0(sK1,k2_tops_1(sK0,sK1))) ),
    inference(superposition,[],[f249,f73])).

fof(f249,plain,(
    k4_xboole_0(k1_tops_1(sK0,sK1),k4_xboole_0(sK1,k2_tops_1(sK0,sK1))) != k4_xboole_0(sK1,k2_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))) ),
    inference(backward_demodulation,[],[f109,f247])).

fof(f247,plain,(
    k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f244,f229])).

fof(f229,plain,(
    k2_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f85,f87,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f85,plain,(
    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f55,f56,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
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

fof(f244,plain,(
    k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f241,f233])).

fof(f233,plain,(
    k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f85,f87,f78])).

fof(f241,plain,(
    k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f85,f87,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_subset_1)).

fof(f109,plain,(
    k4_xboole_0(k1_tops_1(sK0,sK1),k4_xboole_0(sK1,k2_tops_1(sK0,sK1))) != k4_xboole_0(sK1,k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f108,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f108,plain,(
    k4_xboole_0(k1_tops_1(sK0,sK1),k4_xboole_0(sK1,k2_tops_1(sK0,sK1))) != k4_xboole_0(k4_xboole_0(sK1,k2_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f106,f93])).

fof(f93,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(unit_resulting_resolution,[],[f56,f75])).

fof(f106,plain,(
    k4_xboole_0(k1_tops_1(sK0,sK1),k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))) != k4_xboole_0(k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f57,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).

fof(f57,plain,(
    k1_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f53])).
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
% 0.14/0.35  % DateTime   : Tue Dec  1 15:26:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (26868)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (26883)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.52  % (26876)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.54  % (26866)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (26863)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (26869)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (26865)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (26886)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.54  % (26878)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.55  % (26864)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.55  % (26879)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  % (26891)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.55  % (26884)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.55  % (26881)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.55  % (26870)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.55  % (26871)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.55  % (26885)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.56  % (26877)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.56  % (26872)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.56  % (26887)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.56  % (26890)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.56  % (26892)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.56  % (26889)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.56  % (26874)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.56  % (26880)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.56  % (26888)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.57  % (26875)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.58  % (26873)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.58  % (26867)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.59  % (26889)Refutation found. Thanks to Tanya!
% 0.22/0.59  % SZS status Theorem for theBenchmark
% 0.22/0.59  % SZS output start Proof for theBenchmark
% 0.22/0.59  fof(f455,plain,(
% 0.22/0.59    $false),
% 0.22/0.59    inference(subsumption_resolution,[],[f449,f113])).
% 0.22/0.59  fof(f113,plain,(
% 0.22/0.59    k1_xboole_0 = k4_xboole_0(sK1,k2_pre_topc(sK0,sK1))),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f80,f73])).
% 0.22/0.59  fof(f73,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f54])).
% 0.22/0.59  fof(f54,plain,(
% 0.22/0.59    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.22/0.59    inference(nnf_transformation,[],[f3])).
% 0.22/0.59  fof(f3,axiom,(
% 0.22/0.59    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).
% 0.22/0.59  fof(f80,plain,(
% 0.22/0.59    r1_tarski(sK1,k2_pre_topc(sK0,sK1))),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f55,f56,f58])).
% 0.22/0.59  fof(f58,plain,(
% 0.22/0.59    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f25])).
% 0.22/0.59  fof(f25,plain,(
% 0.22/0.59    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.59    inference(ennf_transformation,[],[f15])).
% 0.22/0.59  fof(f15,axiom,(
% 0.22/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).
% 0.22/0.59  fof(f56,plain,(
% 0.22/0.59    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.59    inference(cnf_transformation,[],[f53])).
% 0.22/0.59  fof(f53,plain,(
% 0.22/0.59    (k1_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.22/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f52,f51])).
% 0.22/0.59  fof(f51,plain,(
% 0.22/0.59    ? [X0] : (? [X1] : (k1_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (k1_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k2_tops_1(sK0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.22/0.59    introduced(choice_axiom,[])).
% 0.22/0.59  fof(f52,plain,(
% 0.22/0.59    ? [X1] : (k1_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k2_tops_1(sK0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (k1_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.59    introduced(choice_axiom,[])).
% 0.22/0.59  fof(f24,plain,(
% 0.22/0.59    ? [X0] : (? [X1] : (k1_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.22/0.59    inference(ennf_transformation,[],[f23])).
% 0.22/0.59  fof(f23,negated_conjecture,(
% 0.22/0.59    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 0.22/0.59    inference(negated_conjecture,[],[f22])).
% 0.22/0.59  fof(f22,conjecture,(
% 0.22/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).
% 0.22/0.59  fof(f55,plain,(
% 0.22/0.59    l1_pre_topc(sK0)),
% 0.22/0.59    inference(cnf_transformation,[],[f53])).
% 0.22/0.59  fof(f449,plain,(
% 0.22/0.59    k1_xboole_0 != k4_xboole_0(sK1,k2_pre_topc(sK0,sK1))),
% 0.22/0.59    inference(backward_demodulation,[],[f429,f448])).
% 0.22/0.59  fof(f448,plain,(
% 0.22/0.59    k2_pre_topc(sK0,sK1) = k2_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))),
% 0.22/0.59    inference(forward_demodulation,[],[f447,f418])).
% 0.22/0.59  fof(f418,plain,(
% 0.22/0.59    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 0.22/0.59    inference(backward_demodulation,[],[f264,f409])).
% 0.22/0.59  fof(f409,plain,(
% 0.22/0.59    k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k4_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1)))),
% 0.22/0.59    inference(backward_demodulation,[],[f103,f408])).
% 0.22/0.59  fof(f408,plain,(
% 0.22/0.59    k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k4_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1))),
% 0.22/0.59    inference(forward_demodulation,[],[f407,f216])).
% 0.22/0.59  fof(f216,plain,(
% 0.22/0.59    k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) = k4_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1))),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f87,f65])).
% 0.22/0.59  fof(f65,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.59    inference(cnf_transformation,[],[f32])).
% 0.22/0.59  fof(f32,plain,(
% 0.22/0.59    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.59    inference(ennf_transformation,[],[f8])).
% 0.22/0.59  fof(f8,axiom,(
% 0.22/0.59    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.22/0.59  fof(f87,plain,(
% 0.22/0.59    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f55,f56,f71])).
% 0.22/0.59  fof(f71,plain,(
% 0.22/0.59    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f41])).
% 0.22/0.59  fof(f41,plain,(
% 0.22/0.59    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.59    inference(flattening,[],[f40])).
% 0.22/0.59  fof(f40,plain,(
% 0.22/0.59    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.22/0.59    inference(ennf_transformation,[],[f18])).
% 0.22/0.59  fof(f18,axiom,(
% 0.22/0.59    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).
% 0.22/0.59  fof(f407,plain,(
% 0.22/0.59    k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))),
% 0.22/0.59    inference(subsumption_resolution,[],[f398,f277])).
% 0.22/0.59  fof(f277,plain,(
% 0.22/0.59    m1_subset_1(k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f55,f102,f70])).
% 0.22/0.59  fof(f70,plain,(
% 0.22/0.59    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f39])).
% 0.22/0.59  fof(f39,plain,(
% 0.22/0.59    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.59    inference(flattening,[],[f38])).
% 0.22/0.59  fof(f38,plain,(
% 0.22/0.59    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.22/0.59    inference(ennf_transformation,[],[f14])).
% 0.22/0.59  fof(f14,axiom,(
% 0.22/0.59    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.22/0.59  fof(f102,plain,(
% 0.22/0.59    m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.59    inference(forward_demodulation,[],[f88,f89])).
% 0.22/0.59  fof(f89,plain,(
% 0.22/0.59    k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1)),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f56,f65])).
% 0.22/0.59  fof(f88,plain,(
% 0.22/0.59    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f56,f64])).
% 0.22/0.59  fof(f64,plain,(
% 0.22/0.59    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.59    inference(cnf_transformation,[],[f31])).
% 0.22/0.59  fof(f31,plain,(
% 0.22/0.59    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.59    inference(ennf_transformation,[],[f9])).
% 0.22/0.59  fof(f9,axiom,(
% 0.22/0.59    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.22/0.59  fof(f398,plain,(
% 0.22/0.59    k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) | ~m1_subset_1(k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.59    inference(superposition,[],[f66,f104])).
% 0.22/0.59  fof(f104,plain,(
% 0.22/0.59    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)))),
% 0.22/0.59    inference(forward_demodulation,[],[f83,f89])).
% 0.22/0.59  fof(f83,plain,(
% 0.22/0.59    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f55,f56,f61])).
% 0.22/0.59  fof(f61,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f28])).
% 0.22/0.59  fof(f28,plain,(
% 0.22/0.59    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.59    inference(ennf_transformation,[],[f16])).
% 0.22/0.59  fof(f16,axiom,(
% 0.22/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).
% 0.22/0.59  fof(f66,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.59    inference(cnf_transformation,[],[f33])).
% 0.22/0.59  fof(f33,plain,(
% 0.22/0.59    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.59    inference(ennf_transformation,[],[f10])).
% 0.22/0.59  fof(f10,axiom,(
% 0.22/0.59    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.22/0.59  fof(f103,plain,(
% 0.22/0.59    k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)))),
% 0.22/0.59    inference(forward_demodulation,[],[f84,f89])).
% 0.22/0.59  fof(f84,plain,(
% 0.22/0.59    k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f55,f56,f62])).
% 0.22/0.59  fof(f62,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f29])).
% 0.22/0.59  fof(f29,plain,(
% 0.22/0.59    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.59    inference(ennf_transformation,[],[f17])).
% 0.22/0.59  fof(f17,axiom,(
% 0.22/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_1)).
% 0.22/0.59  fof(f264,plain,(
% 0.22/0.59    k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k4_xboole_0(u1_struct_0(sK0),k1_tops_1(sK0,sK1)))),
% 0.22/0.59    inference(backward_demodulation,[],[f254,f216])).
% 0.22/0.59  fof(f254,plain,(
% 0.22/0.59    k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 0.22/0.59    inference(forward_demodulation,[],[f222,f173])).
% 0.22/0.59  fof(f173,plain,(
% 0.22/0.59    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0) = k4_xboole_0(k2_pre_topc(sK0,sK1),X0)) )),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f86,f75])).
% 0.22/0.59  fof(f75,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.59    inference(cnf_transformation,[],[f42])).
% 0.22/0.59  fof(f42,plain,(
% 0.22/0.59    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.59    inference(ennf_transformation,[],[f12])).
% 0.22/0.59  fof(f12,axiom,(
% 0.22/0.59    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.22/0.59  fof(f86,plain,(
% 0.22/0.59    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f55,f56,f70])).
% 0.22/0.59  fof(f222,plain,(
% 0.22/0.59    k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)))),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f86,f87,f67])).
% 0.22/0.59  fof(f67,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.59    inference(cnf_transformation,[],[f34])).
% 0.22/0.59  fof(f34,plain,(
% 0.22/0.59    ! [X0,X1] : (! [X2] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.59    inference(ennf_transformation,[],[f13])).
% 0.22/0.59  fof(f13,axiom,(
% 0.22/0.59    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).
% 0.22/0.59  fof(f447,plain,(
% 0.22/0.59    k2_pre_topc(sK0,sK1) = k2_xboole_0(k1_tops_1(sK0,sK1),k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)))),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f115,f63])).
% 0.22/0.59  fof(f63,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f30])).
% 0.22/0.59  fof(f30,plain,(
% 0.22/0.59    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.59    inference(ennf_transformation,[],[f5])).
% 0.22/0.59  fof(f5,axiom,(
% 0.22/0.59    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).
% 0.22/0.59  fof(f115,plain,(
% 0.22/0.59    r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1))),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f80,f81,f77])).
% 0.22/0.59  fof(f77,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f46])).
% 0.22/0.59  fof(f46,plain,(
% 0.22/0.59    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.59    inference(flattening,[],[f45])).
% 0.22/0.59  fof(f45,plain,(
% 0.22/0.59    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.59    inference(ennf_transformation,[],[f1])).
% 0.22/0.59  fof(f1,axiom,(
% 0.22/0.59    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.22/0.59  fof(f81,plain,(
% 0.22/0.59    r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f55,f56,f59])).
% 0.22/0.59  fof(f59,plain,(
% 0.22/0.59    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f26])).
% 0.22/0.59  fof(f26,plain,(
% 0.22/0.59    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.59    inference(ennf_transformation,[],[f20])).
% 0.22/0.59  fof(f20,axiom,(
% 0.22/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).
% 0.22/0.59  fof(f429,plain,(
% 0.22/0.59    k1_xboole_0 != k4_xboole_0(sK1,k2_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)))),
% 0.22/0.59    inference(subsumption_resolution,[],[f426,f118])).
% 0.22/0.59  fof(f118,plain,(
% 0.22/0.59    r1_tarski(k1_tops_1(sK0,sK1),k4_xboole_0(sK1,k2_tops_1(sK0,sK1)))),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f81,f82,f76])).
% 0.22/0.59  fof(f76,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f44])).
% 0.22/0.59  fof(f44,plain,(
% 0.22/0.59    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.59    inference(flattening,[],[f43])).
% 0.22/0.59  fof(f43,plain,(
% 0.22/0.59    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.59    inference(ennf_transformation,[],[f6])).
% 0.22/0.59  fof(f6,axiom,(
% 0.22/0.59    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).
% 0.22/0.59  fof(f82,plain,(
% 0.22/0.59    r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f55,f56,f60])).
% 0.22/0.59  fof(f60,plain,(
% 0.22/0.59    ( ! [X0,X1] : (r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f27])).
% 0.22/0.59  fof(f27,plain,(
% 0.22/0.59    ! [X0] : (! [X1] : (r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.59    inference(ennf_transformation,[],[f21])).
% 0.22/0.59  fof(f21,axiom,(
% 0.22/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_tops_1)).
% 0.22/0.59  fof(f426,plain,(
% 0.22/0.59    k1_xboole_0 != k4_xboole_0(sK1,k2_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))) | ~r1_tarski(k1_tops_1(sK0,sK1),k4_xboole_0(sK1,k2_tops_1(sK0,sK1)))),
% 0.22/0.59    inference(superposition,[],[f249,f73])).
% 0.22/0.59  fof(f249,plain,(
% 0.22/0.59    k4_xboole_0(k1_tops_1(sK0,sK1),k4_xboole_0(sK1,k2_tops_1(sK0,sK1))) != k4_xboole_0(sK1,k2_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)))),
% 0.22/0.59    inference(backward_demodulation,[],[f109,f247])).
% 0.22/0.59  fof(f247,plain,(
% 0.22/0.59    k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))),
% 0.22/0.59    inference(backward_demodulation,[],[f244,f229])).
% 0.22/0.59  fof(f229,plain,(
% 0.22/0.59    k2_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f85,f87,f78])).
% 0.22/0.59  fof(f78,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.59    inference(cnf_transformation,[],[f48])).
% 0.22/0.59  fof(f48,plain,(
% 0.22/0.59    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.59    inference(flattening,[],[f47])).
% 0.22/0.59  fof(f47,plain,(
% 0.22/0.59    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.22/0.59    inference(ennf_transformation,[],[f11])).
% 0.22/0.59  fof(f11,axiom,(
% 0.22/0.59    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.22/0.59  fof(f85,plain,(
% 0.22/0.59    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f55,f56,f69])).
% 0.22/0.59  fof(f69,plain,(
% 0.22/0.59    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f37])).
% 0.22/0.59  fof(f37,plain,(
% 0.22/0.59    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.59    inference(flattening,[],[f36])).
% 0.22/0.59  fof(f36,plain,(
% 0.22/0.59    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.22/0.59    inference(ennf_transformation,[],[f19])).
% 0.22/0.59  fof(f19,axiom,(
% 0.22/0.59    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 0.22/0.59  fof(f244,plain,(
% 0.22/0.59    k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))),
% 0.22/0.59    inference(backward_demodulation,[],[f241,f233])).
% 0.22/0.59  fof(f233,plain,(
% 0.22/0.59    k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f85,f87,f78])).
% 0.22/0.59  fof(f241,plain,(
% 0.22/0.59    k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f85,f87,f79])).
% 0.22/0.59  fof(f79,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.59    inference(cnf_transformation,[],[f50])).
% 0.22/0.59  fof(f50,plain,(
% 0.22/0.59    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.59    inference(flattening,[],[f49])).
% 0.22/0.59  fof(f49,plain,(
% 0.22/0.59    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.22/0.59    inference(ennf_transformation,[],[f7])).
% 0.22/0.59  fof(f7,axiom,(
% 0.22/0.59    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_subset_1)).
% 0.22/0.59  fof(f109,plain,(
% 0.22/0.59    k4_xboole_0(k1_tops_1(sK0,sK1),k4_xboole_0(sK1,k2_tops_1(sK0,sK1))) != k4_xboole_0(sK1,k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)))),
% 0.22/0.59    inference(forward_demodulation,[],[f108,f74])).
% 0.22/0.59  fof(f74,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.59    inference(cnf_transformation,[],[f4])).
% 0.22/0.59  fof(f4,axiom,(
% 0.22/0.59    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.22/0.59  fof(f108,plain,(
% 0.22/0.59    k4_xboole_0(k1_tops_1(sK0,sK1),k4_xboole_0(sK1,k2_tops_1(sK0,sK1))) != k4_xboole_0(k4_xboole_0(sK1,k2_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1))),
% 0.22/0.59    inference(forward_demodulation,[],[f106,f93])).
% 0.22/0.59  fof(f93,plain,(
% 0.22/0.59    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)) )),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f56,f75])).
% 0.22/0.59  fof(f106,plain,(
% 0.22/0.59    k4_xboole_0(k1_tops_1(sK0,sK1),k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))) != k4_xboole_0(k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1))),
% 0.22/0.59    inference(unit_resulting_resolution,[],[f57,f68])).
% 0.22/0.59  fof(f68,plain,(
% 0.22/0.59    ( ! [X0,X1] : (X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f35])).
% 0.22/0.59  fof(f35,plain,(
% 0.22/0.59    ! [X0,X1] : (X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0))),
% 0.22/0.59    inference(ennf_transformation,[],[f2])).
% 0.22/0.59  fof(f2,axiom,(
% 0.22/0.59    ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) => X0 = X1)),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).
% 0.22/0.59  fof(f57,plain,(
% 0.22/0.59    k1_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 0.22/0.59    inference(cnf_transformation,[],[f53])).
% 0.22/0.59  % SZS output end Proof for theBenchmark
% 0.22/0.59  % (26889)------------------------------
% 0.22/0.59  % (26889)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (26889)Termination reason: Refutation
% 0.22/0.59  
% 0.22/0.59  % (26889)Memory used [KB]: 11001
% 0.22/0.59  % (26889)Time elapsed: 0.175 s
% 0.22/0.59  % (26889)------------------------------
% 0.22/0.59  % (26889)------------------------------
% 0.22/0.59  % (26862)Success in time 0.23 s
%------------------------------------------------------------------------------
