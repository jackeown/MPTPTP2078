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
% DateTime   : Thu Dec  3 13:11:31 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 241 expanded)
%              Number of leaves         :   15 (  71 expanded)
%              Depth                    :   14
%              Number of atoms          :  178 ( 752 expanded)
%              Number of equality atoms :   62 ( 213 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f168,plain,(
    $false ),
    inference(subsumption_resolution,[],[f167,f38])).

fof(f38,plain,(
    k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f30,f29])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_tops_1(X0,k2_tops_1(X0,X1)) != k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( k2_tops_1(sK0,k2_tops_1(sK0,X1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X1)))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X1] :
        ( k2_tops_1(sK0,k2_tops_1(sK0,X1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X1)))
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_tops_1(X0,k2_tops_1(X0,X1)) != k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_tops_1(X0,k2_tops_1(X0,X1)) != k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => k2_tops_1(X0,k2_tops_1(X0,X1)) = k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,k2_tops_1(X0,X1)) = k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_tops_1)).

fof(f167,plain,(
    k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f166,f120])).

fof(f120,plain,(
    ! [X3] : k4_xboole_0(X3,k1_xboole_0) = X3 ),
    inference(forward_demodulation,[],[f113,f72])).

fof(f72,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f70,f67])).

fof(f67,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) ),
    inference(forward_demodulation,[],[f65,f58])).

fof(f58,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(resolution,[],[f53,f55])).

fof(f55,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
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

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f65,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k3_subset_1(X0,X0) ),
    inference(resolution,[],[f46,f57])).

fof(f57,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f40,f39])).

fof(f39,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f40,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f70,plain,(
    ! [X0] : k3_subset_1(X0,k3_subset_1(X0,X0)) = X0 ),
    inference(resolution,[],[f47,f57])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f113,plain,(
    ! [X3] : k4_xboole_0(X3,k1_xboole_0) = k3_subset_1(X3,k1_xboole_0) ),
    inference(resolution,[],[f68,f46])).

fof(f68,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(backward_demodulation,[],[f63,f67])).

fof(f63,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,X0),k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f45,f57])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f166,plain,(
    k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k4_xboole_0(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_xboole_0) ),
    inference(backward_demodulation,[],[f165,f160])).

fof(f160,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),X0) = k4_xboole_0(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),X0) ),
    inference(resolution,[],[f103,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f103,plain,(
    m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f88,f75])).

fof(f75,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f48,f36])).

fof(f36,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f88,plain,(
    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f75,f37])).

fof(f37,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f165,plain,(
    k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f164,f101])).

fof(f101,plain,(
    k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    inference(resolution,[],[f88,f79])).

fof(f79,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_tops_1(sK0,X0) = k2_pre_topc(sK0,k2_tops_1(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f78,f36])).

fof(f78,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | k2_tops_1(sK0,X0) = k2_pre_topc(sK0,k2_tops_1(sK0,X0)) ) ),
    inference(resolution,[],[f43,f35])).

fof(f35,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k2_tops_1(X0,X1) = k2_pre_topc(X0,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k2_pre_topc(X0,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k2_pre_topc(X0,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k2_pre_topc(X0,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l79_tops_1)).

fof(f164,plain,(
    k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k1_xboole_0) ),
    inference(forward_demodulation,[],[f156,f91])).

fof(f91,plain,(
    k1_xboole_0 = k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    inference(resolution,[],[f77,f37])).

fof(f77,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_xboole_0 = k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X0))) ) ),
    inference(subsumption_resolution,[],[f76,f36])).

fof(f76,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | k1_xboole_0 = k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X0))) ) ),
    inference(resolution,[],[f42,f35])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l80_tops_1)).

fof(f156,plain,(
    k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) ),
    inference(resolution,[],[f103,f87])).

fof(f87,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) ) ),
    inference(resolution,[],[f41,f36])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 19:58:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.37  ipcrm: permission denied for id (819691521)
% 0.13/0.37  ipcrm: permission denied for id (819724290)
% 0.13/0.37  ipcrm: permission denied for id (823361539)
% 0.13/0.37  ipcrm: permission denied for id (819789829)
% 0.13/0.37  ipcrm: permission denied for id (819822598)
% 0.13/0.38  ipcrm: permission denied for id (823427079)
% 0.13/0.38  ipcrm: permission denied for id (819855368)
% 0.13/0.38  ipcrm: permission denied for id (825557001)
% 0.13/0.38  ipcrm: permission denied for id (819888138)
% 0.13/0.38  ipcrm: permission denied for id (819920907)
% 0.13/0.38  ipcrm: permission denied for id (819986445)
% 0.13/0.38  ipcrm: permission denied for id (820019214)
% 0.13/0.39  ipcrm: permission denied for id (820084752)
% 0.13/0.39  ipcrm: permission denied for id (823558161)
% 0.21/0.39  ipcrm: permission denied for id (823590930)
% 0.21/0.39  ipcrm: permission denied for id (820150292)
% 0.21/0.39  ipcrm: permission denied for id (820183061)
% 0.21/0.39  ipcrm: permission denied for id (823656470)
% 0.21/0.40  ipcrm: permission denied for id (820215831)
% 0.21/0.40  ipcrm: permission denied for id (820248600)
% 0.21/0.40  ipcrm: permission denied for id (820281369)
% 0.21/0.40  ipcrm: permission denied for id (820346907)
% 0.21/0.40  ipcrm: permission denied for id (825720860)
% 0.21/0.40  ipcrm: permission denied for id (820412445)
% 0.21/0.40  ipcrm: permission denied for id (825786399)
% 0.21/0.41  ipcrm: permission denied for id (820510752)
% 0.21/0.41  ipcrm: permission denied for id (820543521)
% 0.21/0.41  ipcrm: permission denied for id (823820322)
% 0.21/0.41  ipcrm: permission denied for id (820609059)
% 0.21/0.41  ipcrm: permission denied for id (820641828)
% 0.21/0.41  ipcrm: permission denied for id (823853093)
% 0.21/0.41  ipcrm: permission denied for id (820707366)
% 0.21/0.42  ipcrm: permission denied for id (820772904)
% 0.21/0.42  ipcrm: permission denied for id (820805673)
% 0.21/0.42  ipcrm: permission denied for id (823951403)
% 0.21/0.42  ipcrm: permission denied for id (820871212)
% 0.21/0.42  ipcrm: permission denied for id (823984173)
% 0.21/0.42  ipcrm: permission denied for id (820936750)
% 0.21/0.42  ipcrm: permission denied for id (825884719)
% 0.21/0.43  ipcrm: permission denied for id (821002288)
% 0.21/0.43  ipcrm: permission denied for id (824049713)
% 0.21/0.43  ipcrm: permission denied for id (821035058)
% 0.21/0.43  ipcrm: permission denied for id (821067827)
% 0.21/0.43  ipcrm: permission denied for id (821133364)
% 0.21/0.43  ipcrm: permission denied for id (821166133)
% 0.21/0.43  ipcrm: permission denied for id (825917494)
% 0.21/0.43  ipcrm: permission denied for id (821231671)
% 0.21/0.43  ipcrm: permission denied for id (821264440)
% 0.21/0.44  ipcrm: permission denied for id (821297209)
% 0.21/0.44  ipcrm: permission denied for id (821329978)
% 0.21/0.44  ipcrm: permission denied for id (825950267)
% 0.21/0.44  ipcrm: permission denied for id (821395516)
% 0.21/0.44  ipcrm: permission denied for id (824148029)
% 0.21/0.44  ipcrm: permission denied for id (824180798)
% 0.21/0.44  ipcrm: permission denied for id (824246336)
% 0.21/0.45  ipcrm: permission denied for id (824279105)
% 0.21/0.45  ipcrm: permission denied for id (824311874)
% 0.21/0.45  ipcrm: permission denied for id (821624899)
% 0.21/0.45  ipcrm: permission denied for id (821657668)
% 0.21/0.45  ipcrm: permission denied for id (824377413)
% 0.21/0.45  ipcrm: permission denied for id (821690438)
% 0.21/0.45  ipcrm: permission denied for id (824410183)
% 0.21/0.45  ipcrm: permission denied for id (821755976)
% 0.21/0.46  ipcrm: permission denied for id (821788745)
% 0.21/0.46  ipcrm: permission denied for id (821821514)
% 0.21/0.46  ipcrm: permission denied for id (824475724)
% 0.21/0.46  ipcrm: permission denied for id (826048589)
% 0.21/0.46  ipcrm: permission denied for id (824541262)
% 0.21/0.46  ipcrm: permission denied for id (826081359)
% 0.21/0.46  ipcrm: permission denied for id (821952592)
% 0.21/0.47  ipcrm: permission denied for id (821985361)
% 0.21/0.47  ipcrm: permission denied for id (822018130)
% 0.21/0.47  ipcrm: permission denied for id (824606803)
% 0.21/0.47  ipcrm: permission denied for id (824705109)
% 0.21/0.47  ipcrm: permission denied for id (824737878)
% 0.21/0.47  ipcrm: permission denied for id (822149207)
% 0.21/0.47  ipcrm: permission denied for id (822214744)
% 0.21/0.48  ipcrm: permission denied for id (822247513)
% 0.21/0.48  ipcrm: permission denied for id (822280282)
% 0.21/0.48  ipcrm: permission denied for id (822313052)
% 0.21/0.48  ipcrm: permission denied for id (822345821)
% 0.21/0.48  ipcrm: permission denied for id (826179678)
% 0.21/0.48  ipcrm: permission denied for id (824836191)
% 0.21/0.49  ipcrm: permission denied for id (824901729)
% 0.21/0.49  ipcrm: permission denied for id (826277986)
% 0.21/0.49  ipcrm: permission denied for id (822542435)
% 0.21/0.49  ipcrm: permission denied for id (826310756)
% 0.21/0.49  ipcrm: permission denied for id (822607973)
% 0.21/0.49  ipcrm: permission denied for id (822640742)
% 0.21/0.49  ipcrm: permission denied for id (825000039)
% 0.21/0.49  ipcrm: permission denied for id (822673512)
% 0.21/0.50  ipcrm: permission denied for id (825032809)
% 0.21/0.50  ipcrm: permission denied for id (826343530)
% 0.21/0.50  ipcrm: permission denied for id (826376299)
% 0.21/0.50  ipcrm: permission denied for id (822771820)
% 0.21/0.50  ipcrm: permission denied for id (825131117)
% 0.21/0.50  ipcrm: permission denied for id (822837358)
% 0.21/0.50  ipcrm: permission denied for id (826409071)
% 0.21/0.50  ipcrm: permission denied for id (822870128)
% 0.21/0.51  ipcrm: permission denied for id (822902897)
% 0.21/0.51  ipcrm: permission denied for id (825196658)
% 0.21/0.51  ipcrm: permission denied for id (822935667)
% 0.21/0.51  ipcrm: permission denied for id (823001205)
% 0.21/0.51  ipcrm: permission denied for id (825262198)
% 0.21/0.51  ipcrm: permission denied for id (823066743)
% 0.21/0.51  ipcrm: permission denied for id (825294968)
% 0.21/0.51  ipcrm: permission denied for id (823132281)
% 0.21/0.52  ipcrm: permission denied for id (825327738)
% 0.21/0.52  ipcrm: permission denied for id (825360507)
% 0.35/0.52  ipcrm: permission denied for id (826474620)
% 0.35/0.52  ipcrm: permission denied for id (826540158)
% 0.35/0.52  ipcrm: permission denied for id (823296127)
% 0.38/0.64  % (15913)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.38/0.64  % (15913)Refutation not found, incomplete strategy% (15913)------------------------------
% 0.38/0.64  % (15913)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.38/0.64  % (15913)Termination reason: Refutation not found, incomplete strategy
% 0.38/0.64  
% 0.38/0.64  % (15913)Memory used [KB]: 1663
% 0.38/0.64  % (15913)Time elapsed: 0.082 s
% 0.38/0.64  % (15913)------------------------------
% 0.38/0.64  % (15913)------------------------------
% 0.38/0.66  % (15920)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.38/0.67  % (15934)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.38/0.67  % (15927)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.38/0.67  % (15936)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.38/0.68  % (15936)Refutation not found, incomplete strategy% (15936)------------------------------
% 0.38/0.68  % (15936)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.38/0.68  % (15936)Termination reason: Refutation not found, incomplete strategy
% 0.38/0.68  
% 0.38/0.68  % (15936)Memory used [KB]: 10746
% 0.38/0.68  % (15936)Time elapsed: 0.116 s
% 0.38/0.68  % (15936)------------------------------
% 0.38/0.68  % (15936)------------------------------
% 0.38/0.68  % (15929)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.38/0.68  % (15914)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.38/0.68  % (15918)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.38/0.68  % (15916)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.38/0.69  % (15923)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.46/0.69  % (15931)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.46/0.69  % (15924)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.46/0.70  % (15919)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.46/0.70  % (15912)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.46/0.70  % (15921)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.46/0.70  % (15932)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.46/0.71  % (15915)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.46/0.71  % (15939)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.46/0.71  % (15937)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.46/0.71  % (15935)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.46/0.71  % (15928)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.46/0.71  % (15939)Refutation not found, incomplete strategy% (15939)------------------------------
% 0.46/0.71  % (15939)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.46/0.71  % (15939)Termination reason: Refutation not found, incomplete strategy
% 0.46/0.71  
% 0.46/0.71  % (15939)Memory used [KB]: 6140
% 0.46/0.71  % (15939)Time elapsed: 0.123 s
% 0.46/0.71  % (15939)------------------------------
% 0.46/0.71  % (15939)------------------------------
% 0.46/0.71  % (15928)Refutation not found, incomplete strategy% (15928)------------------------------
% 0.46/0.71  % (15928)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.46/0.71  % (15928)Termination reason: Refutation not found, incomplete strategy
% 0.46/0.71  
% 0.46/0.71  % (15928)Memory used [KB]: 10618
% 0.46/0.71  % (15928)Time elapsed: 0.143 s
% 0.46/0.71  % (15928)------------------------------
% 0.46/0.71  % (15928)------------------------------
% 0.46/0.71  % (15930)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.46/0.72  % (15922)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.46/0.72  % (15919)Refutation found. Thanks to Tanya!
% 0.46/0.72  % SZS status Theorem for theBenchmark
% 0.46/0.72  % SZS output start Proof for theBenchmark
% 0.46/0.72  fof(f168,plain,(
% 0.46/0.72    $false),
% 0.46/0.72    inference(subsumption_resolution,[],[f167,f38])).
% 0.46/0.72  fof(f38,plain,(
% 0.46/0.72    k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))),
% 0.46/0.72    inference(cnf_transformation,[],[f31])).
% 0.46/0.72  fof(f31,plain,(
% 0.46/0.72    (k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.46/0.72    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f30,f29])).
% 0.46/0.72  fof(f29,plain,(
% 0.46/0.72    ? [X0] : (? [X1] : (k2_tops_1(X0,k2_tops_1(X0,X1)) != k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (k2_tops_1(sK0,k2_tops_1(sK0,X1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.46/0.72    introduced(choice_axiom,[])).
% 0.46/0.72  fof(f30,plain,(
% 0.46/0.72    ? [X1] : (k2_tops_1(sK0,k2_tops_1(sK0,X1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.46/0.72    introduced(choice_axiom,[])).
% 0.46/0.72  fof(f17,plain,(
% 0.46/0.72    ? [X0] : (? [X1] : (k2_tops_1(X0,k2_tops_1(X0,X1)) != k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.46/0.72    inference(flattening,[],[f16])).
% 0.46/0.72  fof(f16,plain,(
% 0.46/0.72    ? [X0] : (? [X1] : (k2_tops_1(X0,k2_tops_1(X0,X1)) != k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.46/0.72    inference(ennf_transformation,[],[f15])).
% 0.46/0.72  fof(f15,negated_conjecture,(
% 0.46/0.72    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,k2_tops_1(X0,X1)) = k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))))),
% 0.46/0.72    inference(negated_conjecture,[],[f14])).
% 0.46/0.72  fof(f14,conjecture,(
% 0.46/0.72    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,k2_tops_1(X0,X1)) = k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))))),
% 0.46/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_tops_1)).
% 0.46/0.72  fof(f167,plain,(
% 0.46/0.72    k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))),
% 0.46/0.72    inference(forward_demodulation,[],[f166,f120])).
% 0.46/0.72  fof(f120,plain,(
% 0.46/0.72    ( ! [X3] : (k4_xboole_0(X3,k1_xboole_0) = X3) )),
% 0.46/0.72    inference(forward_demodulation,[],[f113,f72])).
% 0.46/0.72  fof(f72,plain,(
% 0.46/0.72    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 0.46/0.72    inference(forward_demodulation,[],[f70,f67])).
% 0.46/0.72  fof(f67,plain,(
% 0.46/0.72    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,X0)) )),
% 0.46/0.72    inference(forward_demodulation,[],[f65,f58])).
% 0.46/0.72  fof(f58,plain,(
% 0.46/0.72    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.46/0.72    inference(resolution,[],[f53,f55])).
% 0.46/0.72  fof(f55,plain,(
% 0.46/0.72    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.46/0.72    inference(equality_resolution,[],[f50])).
% 0.46/0.72  fof(f50,plain,(
% 0.46/0.72    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.46/0.72    inference(cnf_transformation,[],[f33])).
% 0.46/0.72  fof(f33,plain,(
% 0.46/0.72    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.46/0.72    inference(flattening,[],[f32])).
% 0.46/0.72  fof(f32,plain,(
% 0.46/0.72    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.46/0.72    inference(nnf_transformation,[],[f1])).
% 0.46/0.72  fof(f1,axiom,(
% 0.46/0.72    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.46/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.46/0.72  fof(f53,plain,(
% 0.46/0.72    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.46/0.72    inference(cnf_transformation,[],[f34])).
% 0.46/0.72  fof(f34,plain,(
% 0.46/0.72    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.46/0.72    inference(nnf_transformation,[],[f2])).
% 0.46/0.72  fof(f2,axiom,(
% 0.46/0.72    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.46/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.46/0.72  fof(f65,plain,(
% 0.46/0.72    ( ! [X0] : (k4_xboole_0(X0,X0) = k3_subset_1(X0,X0)) )),
% 0.46/0.72    inference(resolution,[],[f46,f57])).
% 0.46/0.72  fof(f57,plain,(
% 0.46/0.72    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.46/0.72    inference(forward_demodulation,[],[f40,f39])).
% 0.46/0.72  fof(f39,plain,(
% 0.46/0.72    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.46/0.72    inference(cnf_transformation,[],[f4])).
% 0.46/0.72  fof(f4,axiom,(
% 0.46/0.72    ! [X0] : k2_subset_1(X0) = X0),
% 0.46/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.46/0.72  fof(f40,plain,(
% 0.46/0.72    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.46/0.72    inference(cnf_transformation,[],[f6])).
% 0.46/0.72  fof(f6,axiom,(
% 0.46/0.72    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.46/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.46/0.72  fof(f46,plain,(
% 0.46/0.72    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.46/0.72    inference(cnf_transformation,[],[f24])).
% 0.46/0.72  fof(f24,plain,(
% 0.46/0.72    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.46/0.72    inference(ennf_transformation,[],[f5])).
% 0.46/0.72  fof(f5,axiom,(
% 0.46/0.72    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.46/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.46/0.72  fof(f70,plain,(
% 0.46/0.72    ( ! [X0] : (k3_subset_1(X0,k3_subset_1(X0,X0)) = X0) )),
% 0.46/0.72    inference(resolution,[],[f47,f57])).
% 0.46/0.72  fof(f47,plain,(
% 0.46/0.72    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.46/0.72    inference(cnf_transformation,[],[f25])).
% 0.46/0.72  fof(f25,plain,(
% 0.46/0.72    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.46/0.72    inference(ennf_transformation,[],[f8])).
% 0.46/0.72  fof(f8,axiom,(
% 0.46/0.72    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.46/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.46/0.72  fof(f113,plain,(
% 0.46/0.72    ( ! [X3] : (k4_xboole_0(X3,k1_xboole_0) = k3_subset_1(X3,k1_xboole_0)) )),
% 0.46/0.72    inference(resolution,[],[f68,f46])).
% 0.46/0.72  fof(f68,plain,(
% 0.46/0.72    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.46/0.72    inference(backward_demodulation,[],[f63,f67])).
% 0.46/0.72  fof(f63,plain,(
% 0.46/0.72    ( ! [X0] : (m1_subset_1(k3_subset_1(X0,X0),k1_zfmisc_1(X0))) )),
% 0.46/0.72    inference(resolution,[],[f45,f57])).
% 0.46/0.72  fof(f45,plain,(
% 0.46/0.72    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.46/0.72    inference(cnf_transformation,[],[f23])).
% 0.46/0.72  fof(f23,plain,(
% 0.46/0.72    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.46/0.72    inference(ennf_transformation,[],[f7])).
% 0.46/0.72  fof(f7,axiom,(
% 0.46/0.72    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.46/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.46/0.72  fof(f166,plain,(
% 0.46/0.72    k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k4_xboole_0(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_xboole_0)),
% 0.46/0.72    inference(backward_demodulation,[],[f165,f160])).
% 0.46/0.72  fof(f160,plain,(
% 0.46/0.72    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),X0) = k4_xboole_0(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),X0)) )),
% 0.46/0.72    inference(resolution,[],[f103,f54])).
% 0.46/0.72  fof(f54,plain,(
% 0.46/0.72    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 0.46/0.72    inference(cnf_transformation,[],[f28])).
% 0.46/0.72  fof(f28,plain,(
% 0.46/0.72    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.46/0.72    inference(ennf_transformation,[],[f9])).
% 0.46/0.72  fof(f9,axiom,(
% 0.46/0.72    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.46/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.46/0.72  fof(f103,plain,(
% 0.46/0.72    m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.46/0.72    inference(resolution,[],[f88,f75])).
% 0.46/0.72  fof(f75,plain,(
% 0.46/0.72    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.46/0.72    inference(resolution,[],[f48,f36])).
% 0.46/0.72  fof(f36,plain,(
% 0.46/0.72    l1_pre_topc(sK0)),
% 0.46/0.72    inference(cnf_transformation,[],[f31])).
% 0.46/0.72  fof(f48,plain,(
% 0.46/0.72    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.46/0.72    inference(cnf_transformation,[],[f27])).
% 0.46/0.72  fof(f27,plain,(
% 0.46/0.72    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.46/0.72    inference(flattening,[],[f26])).
% 0.46/0.72  fof(f26,plain,(
% 0.46/0.72    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.46/0.72    inference(ennf_transformation,[],[f10])).
% 0.46/0.72  fof(f10,axiom,(
% 0.46/0.72    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.46/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 0.46/0.72  fof(f88,plain,(
% 0.46/0.72    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.46/0.72    inference(resolution,[],[f75,f37])).
% 0.46/0.72  fof(f37,plain,(
% 0.46/0.72    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.46/0.72    inference(cnf_transformation,[],[f31])).
% 0.46/0.72  fof(f165,plain,(
% 0.46/0.72    k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_xboole_0)),
% 0.46/0.72    inference(forward_demodulation,[],[f164,f101])).
% 0.46/0.72  fof(f101,plain,(
% 0.46/0.72    k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))),
% 0.46/0.72    inference(resolution,[],[f88,f79])).
% 0.46/0.72  fof(f79,plain,(
% 0.46/0.72    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,X0) = k2_pre_topc(sK0,k2_tops_1(sK0,X0))) )),
% 0.46/0.72    inference(subsumption_resolution,[],[f78,f36])).
% 0.46/0.72  fof(f78,plain,(
% 0.46/0.72    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | k2_tops_1(sK0,X0) = k2_pre_topc(sK0,k2_tops_1(sK0,X0))) )),
% 0.46/0.72    inference(resolution,[],[f43,f35])).
% 0.46/0.72  fof(f35,plain,(
% 0.46/0.72    v2_pre_topc(sK0)),
% 0.46/0.72    inference(cnf_transformation,[],[f31])).
% 0.46/0.72  fof(f43,plain,(
% 0.46/0.72    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k2_tops_1(X0,X1) = k2_pre_topc(X0,k2_tops_1(X0,X1))) )),
% 0.46/0.72    inference(cnf_transformation,[],[f22])).
% 0.46/0.72  fof(f22,plain,(
% 0.46/0.72    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k2_pre_topc(X0,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.46/0.72    inference(flattening,[],[f21])).
% 0.46/0.72  fof(f21,plain,(
% 0.46/0.72    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k2_pre_topc(X0,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.46/0.72    inference(ennf_transformation,[],[f12])).
% 0.46/0.72  fof(f12,axiom,(
% 0.46/0.72    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k2_pre_topc(X0,k2_tops_1(X0,X1))))),
% 0.46/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l79_tops_1)).
% 0.46/0.72  fof(f164,plain,(
% 0.46/0.72    k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k1_xboole_0)),
% 0.46/0.72    inference(forward_demodulation,[],[f156,f91])).
% 0.46/0.72  fof(f91,plain,(
% 0.46/0.72    k1_xboole_0 = k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))),
% 0.46/0.72    inference(resolution,[],[f77,f37])).
% 0.46/0.72  fof(f77,plain,(
% 0.46/0.72    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X0)))) )),
% 0.46/0.72    inference(subsumption_resolution,[],[f76,f36])).
% 0.46/0.72  fof(f76,plain,(
% 0.46/0.72    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | k1_xboole_0 = k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X0)))) )),
% 0.46/0.72    inference(resolution,[],[f42,f35])).
% 0.46/0.72  fof(f42,plain,(
% 0.46/0.72    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))) )),
% 0.46/0.72    inference(cnf_transformation,[],[f20])).
% 0.46/0.72  fof(f20,plain,(
% 0.46/0.72    ! [X0] : (! [X1] : (k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.46/0.72    inference(flattening,[],[f19])).
% 0.46/0.72  fof(f19,plain,(
% 0.46/0.72    ! [X0] : (! [X1] : (k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.46/0.72    inference(ennf_transformation,[],[f13])).
% 0.46/0.72  fof(f13,axiom,(
% 0.46/0.72    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))))),
% 0.46/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l80_tops_1)).
% 0.46/0.72  fof(f156,plain,(
% 0.46/0.72    k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))))),
% 0.46/0.72    inference(resolution,[],[f103,f87])).
% 0.46/0.72  fof(f87,plain,(
% 0.46/0.72    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0))) )),
% 0.46/0.72    inference(resolution,[],[f41,f36])).
% 0.46/0.72  fof(f41,plain,(
% 0.46/0.72    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))) )),
% 0.46/0.72    inference(cnf_transformation,[],[f18])).
% 0.46/0.72  fof(f18,plain,(
% 0.46/0.72    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.46/0.72    inference(ennf_transformation,[],[f11])).
% 0.46/0.72  fof(f11,axiom,(
% 0.46/0.72    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 0.46/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 0.46/0.72  % SZS output end Proof for theBenchmark
% 0.46/0.72  % (15919)------------------------------
% 0.46/0.72  % (15919)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.46/0.72  % (15919)Termination reason: Refutation
% 0.46/0.72  
% 0.46/0.72  % (15919)Memory used [KB]: 1791
% 0.46/0.72  % (15919)Time elapsed: 0.150 s
% 0.46/0.72  % (15919)------------------------------
% 0.46/0.72  % (15919)------------------------------
% 0.46/0.72  % (15922)Refutation not found, incomplete strategy% (15922)------------------------------
% 0.46/0.72  % (15922)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.46/0.72  % (15922)Termination reason: Refutation not found, incomplete strategy
% 0.46/0.72  
% 0.46/0.72  % (15922)Memory used [KB]: 10746
% 0.46/0.72  % (15922)Time elapsed: 0.146 s
% 0.46/0.72  % (15922)------------------------------
% 0.46/0.72  % (15922)------------------------------
% 0.46/0.72  % (15778)Success in time 0.356 s
%------------------------------------------------------------------------------
