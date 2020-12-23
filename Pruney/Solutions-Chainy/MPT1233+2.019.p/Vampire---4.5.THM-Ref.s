%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:59 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 131 expanded)
%              Number of leaves         :   16 (  37 expanded)
%              Depth                    :   13
%              Number of atoms          :  158 ( 293 expanded)
%              Number of equality atoms :   38 (  94 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f88,plain,(
    $false ),
    inference(subsumption_resolution,[],[f87,f58])).

fof(f58,plain,(
    u1_struct_0(sK0) != k1_tops_1(sK0,u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f35,f57])).

fof(f57,plain,(
    k2_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(resolution,[],[f43,f54])).

fof(f54,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f44,f34])).

fof(f34,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f31])).

fof(f31,plain,
    ( ? [X0] :
        ( k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0))
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] :
      ( k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).

fof(f44,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f43,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f35,plain,(
    k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f32])).

fof(f87,plain,(
    u1_struct_0(sK0) = k1_tops_1(sK0,u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f86,f52])).

fof(f52,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f39,f51])).

fof(f51,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f42,f38])).

fof(f38,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(f42,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

fof(f39,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f86,plain,(
    k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0) ),
    inference(backward_demodulation,[],[f77,f82])).

fof(f82,plain,(
    k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0) ),
    inference(resolution,[],[f81,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f81,plain,(
    r1_tarski(k2_pre_topc(sK0,k1_xboole_0),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f80,f34])).

fof(f80,plain,
    ( r1_tarski(k2_pre_topc(sK0,k1_xboole_0),k1_xboole_0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f78,f69])).

fof(f69,plain,(
    v4_pre_topc(k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f68,f33])).

fof(f33,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f68,plain,
    ( v4_pre_topc(k1_xboole_0,sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f67,f34])).

fof(f67,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | v4_pre_topc(k1_xboole_0,X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f65,f36])).

fof(f36,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f65,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | v4_pre_topc(k1_xboole_0,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(resolution,[],[f48,f40])).

fof(f40,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_xboole_0(X1)
      | v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).

fof(f78,plain,(
    ! [X0] :
      ( ~ v4_pre_topc(k1_xboole_0,X0)
      | r1_tarski(k2_pre_topc(X0,k1_xboole_0),k1_xboole_0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f75,f40])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | r1_tarski(k2_pre_topc(X0,k1_xboole_0),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f74,f40])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,k1_xboole_0),X1)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f46,f37])).

fof(f37,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X1)
      | r1_tarski(k2_pre_topc(X0,X2),X1)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X2),X1)
              | ~ r1_tarski(X2,X1)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X2),X1)
              | ~ r1_tarski(X2,X1)
              | ~ v4_pre_topc(X1,X0)
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
             => ( ( r1_tarski(X2,X1)
                  & v4_pre_topc(X1,X0) )
               => r1_tarski(k2_pre_topc(X0,X2),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tops_1)).

fof(f77,plain,(
    k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_xboole_0)) ),
    inference(resolution,[],[f73,f34])).

fof(f73,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(X1)
      | k1_tops_1(X1,u1_struct_0(X1)) = k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f71,f63])).

fof(f63,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) ),
    inference(forward_demodulation,[],[f61,f52])).

fof(f61,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) ),
    inference(resolution,[],[f49,f40])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f71,plain,(
    ! [X1] :
      ( k1_tops_1(X1,u1_struct_0(X1)) = k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),u1_struct_0(X1))))
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f45,f56])).

fof(f56,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f53,f52])).

fof(f53,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f41,f51])).

fof(f41,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:21:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.42  % (32631)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.42  % (32631)Refutation found. Thanks to Tanya!
% 0.20/0.42  % SZS status Theorem for theBenchmark
% 0.20/0.42  % SZS output start Proof for theBenchmark
% 0.20/0.42  fof(f88,plain,(
% 0.20/0.42    $false),
% 0.20/0.42    inference(subsumption_resolution,[],[f87,f58])).
% 0.20/0.42  fof(f58,plain,(
% 0.20/0.42    u1_struct_0(sK0) != k1_tops_1(sK0,u1_struct_0(sK0))),
% 0.20/0.42    inference(backward_demodulation,[],[f35,f57])).
% 0.20/0.42  fof(f57,plain,(
% 0.20/0.42    k2_struct_0(sK0) = u1_struct_0(sK0)),
% 0.20/0.42    inference(resolution,[],[f43,f54])).
% 0.20/0.42  fof(f54,plain,(
% 0.20/0.42    l1_struct_0(sK0)),
% 0.20/0.42    inference(resolution,[],[f44,f34])).
% 0.20/0.42  fof(f34,plain,(
% 0.20/0.42    l1_pre_topc(sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f32])).
% 0.20/0.42  fof(f32,plain,(
% 0.20/0.42    k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.20/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f31])).
% 0.20/0.42  fof(f31,plain,(
% 0.20/0.42    ? [X0] : (k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f19,plain,(
% 0.20/0.42    ? [X0] : (k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.42    inference(flattening,[],[f18])).
% 0.20/0.42  fof(f18,plain,(
% 0.20/0.42    ? [X0] : (k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0)) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.20/0.42    inference(ennf_transformation,[],[f17])).
% 0.20/0.42  fof(f17,negated_conjecture,(
% 0.20/0.42    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)))),
% 0.20/0.42    inference(negated_conjecture,[],[f16])).
% 0.20/0.42  fof(f16,conjecture,(
% 0.20/0.42    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).
% 0.20/0.42  fof(f44,plain,(
% 0.20/0.42    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f21])).
% 0.20/0.42  fof(f21,plain,(
% 0.20/0.42    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.42    inference(ennf_transformation,[],[f13])).
% 0.20/0.42  fof(f13,axiom,(
% 0.20/0.42    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.42  fof(f43,plain,(
% 0.20/0.42    ( ! [X0] : (~l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f20])).
% 0.20/0.42  fof(f20,plain,(
% 0.20/0.42    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.42    inference(ennf_transformation,[],[f12])).
% 0.20/0.42  fof(f12,axiom,(
% 0.20/0.42    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.42  fof(f35,plain,(
% 0.20/0.42    k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0))),
% 0.20/0.42    inference(cnf_transformation,[],[f32])).
% 0.20/0.42  fof(f87,plain,(
% 0.20/0.42    u1_struct_0(sK0) = k1_tops_1(sK0,u1_struct_0(sK0))),
% 0.20/0.42    inference(forward_demodulation,[],[f86,f52])).
% 0.20/0.42  fof(f52,plain,(
% 0.20/0.42    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 0.20/0.42    inference(definition_unfolding,[],[f39,f51])).
% 0.20/0.42  fof(f51,plain,(
% 0.20/0.42    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 0.20/0.42    inference(definition_unfolding,[],[f42,f38])).
% 0.20/0.42  fof(f38,plain,(
% 0.20/0.42    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f4])).
% 0.20/0.42  fof(f4,axiom,(
% 0.20/0.42    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).
% 0.20/0.42  fof(f42,plain,(
% 0.20/0.42    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f8])).
% 0.20/0.42  fof(f8,axiom,(
% 0.20/0.42    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).
% 0.20/0.42  fof(f39,plain,(
% 0.20/0.42    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.20/0.42    inference(cnf_transformation,[],[f5])).
% 0.20/0.42  fof(f5,axiom,(
% 0.20/0.42    ! [X0] : k2_subset_1(X0) = X0),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.20/0.42  fof(f86,plain,(
% 0.20/0.42    k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0)),
% 0.20/0.42    inference(backward_demodulation,[],[f77,f82])).
% 0.20/0.42  fof(f82,plain,(
% 0.20/0.42    k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0)),
% 0.20/0.42    inference(resolution,[],[f81,f47])).
% 0.20/0.42  fof(f47,plain,(
% 0.20/0.42    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.20/0.42    inference(cnf_transformation,[],[f25])).
% 0.20/0.42  fof(f25,plain,(
% 0.20/0.42    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.20/0.42    inference(ennf_transformation,[],[f3])).
% 0.20/0.42  fof(f3,axiom,(
% 0.20/0.42    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.20/0.42  fof(f81,plain,(
% 0.20/0.42    r1_tarski(k2_pre_topc(sK0,k1_xboole_0),k1_xboole_0)),
% 0.20/0.42    inference(subsumption_resolution,[],[f80,f34])).
% 0.20/0.42  fof(f80,plain,(
% 0.20/0.42    r1_tarski(k2_pre_topc(sK0,k1_xboole_0),k1_xboole_0) | ~l1_pre_topc(sK0)),
% 0.20/0.42    inference(resolution,[],[f78,f69])).
% 0.20/0.42  fof(f69,plain,(
% 0.20/0.42    v4_pre_topc(k1_xboole_0,sK0)),
% 0.20/0.42    inference(subsumption_resolution,[],[f68,f33])).
% 0.20/0.42  fof(f33,plain,(
% 0.20/0.42    v2_pre_topc(sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f32])).
% 0.20/0.42  fof(f68,plain,(
% 0.20/0.42    v4_pre_topc(k1_xboole_0,sK0) | ~v2_pre_topc(sK0)),
% 0.20/0.42    inference(resolution,[],[f67,f34])).
% 0.20/0.42  fof(f67,plain,(
% 0.20/0.42    ( ! [X0] : (~l1_pre_topc(X0) | v4_pre_topc(k1_xboole_0,X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.42    inference(subsumption_resolution,[],[f65,f36])).
% 0.20/0.42  fof(f36,plain,(
% 0.20/0.42    v1_xboole_0(k1_xboole_0)),
% 0.20/0.42    inference(cnf_transformation,[],[f1])).
% 0.20/0.42  fof(f1,axiom,(
% 0.20/0.42    v1_xboole_0(k1_xboole_0)),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.42  fof(f65,plain,(
% 0.20/0.42    ( ! [X0] : (~v1_xboole_0(k1_xboole_0) | v4_pre_topc(k1_xboole_0,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.42    inference(resolution,[],[f48,f40])).
% 0.20/0.42  fof(f40,plain,(
% 0.20/0.42    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f9])).
% 0.20/0.42  fof(f9,axiom,(
% 0.20/0.42    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.20/0.42  fof(f48,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1) | v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f27])).
% 0.20/0.42  fof(f27,plain,(
% 0.20/0.42    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.42    inference(flattening,[],[f26])).
% 0.20/0.42  fof(f26,plain,(
% 0.20/0.42    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.42    inference(ennf_transformation,[],[f11])).
% 0.20/0.42  fof(f11,axiom,(
% 0.20/0.42    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v4_pre_topc(X1,X0))))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).
% 0.20/0.42  fof(f78,plain,(
% 0.20/0.42    ( ! [X0] : (~v4_pre_topc(k1_xboole_0,X0) | r1_tarski(k2_pre_topc(X0,k1_xboole_0),k1_xboole_0) | ~l1_pre_topc(X0)) )),
% 0.20/0.42    inference(resolution,[],[f75,f40])).
% 0.20/0.42  fof(f75,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | r1_tarski(k2_pre_topc(X0,k1_xboole_0),X1) | ~l1_pre_topc(X0)) )),
% 0.20/0.42    inference(subsumption_resolution,[],[f74,f40])).
% 0.20/0.42  fof(f74,plain,(
% 0.20/0.42    ( ! [X0,X1] : (r1_tarski(k2_pre_topc(X0,k1_xboole_0),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.42    inference(resolution,[],[f46,f37])).
% 0.20/0.42  fof(f37,plain,(
% 0.20/0.42    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f2])).
% 0.20/0.42  fof(f2,axiom,(
% 0.20/0.42    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.42  fof(f46,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~r1_tarski(X2,X1) | r1_tarski(k2_pre_topc(X0,X2),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f24])).
% 0.20/0.42  fof(f24,plain,(
% 0.20/0.42    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_pre_topc(X0,X2),X1) | ~r1_tarski(X2,X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.42    inference(flattening,[],[f23])).
% 0.20/0.42  fof(f23,plain,(
% 0.20/0.42    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k2_pre_topc(X0,X2),X1) | (~r1_tarski(X2,X1) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.42    inference(ennf_transformation,[],[f15])).
% 0.20/0.42  fof(f15,axiom,(
% 0.20/0.42    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X2,X1) & v4_pre_topc(X1,X0)) => r1_tarski(k2_pre_topc(X0,X2),X1)))))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tops_1)).
% 0.20/0.42  fof(f77,plain,(
% 0.20/0.42    k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_xboole_0))),
% 0.20/0.42    inference(resolution,[],[f73,f34])).
% 0.20/0.42  fof(f73,plain,(
% 0.20/0.42    ( ! [X1] : (~l1_pre_topc(X1) | k1_tops_1(X1,u1_struct_0(X1)) = k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k1_xboole_0))) )),
% 0.20/0.42    inference(forward_demodulation,[],[f71,f63])).
% 0.20/0.42  fof(f63,plain,(
% 0.20/0.42    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,X0)) )),
% 0.20/0.42    inference(forward_demodulation,[],[f61,f52])).
% 0.20/0.42  fof(f61,plain,(
% 0.20/0.42    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0))) )),
% 0.20/0.42    inference(resolution,[],[f49,f40])).
% 0.20/0.42  fof(f49,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.20/0.42    inference(cnf_transformation,[],[f28])).
% 0.20/0.42  fof(f28,plain,(
% 0.20/0.42    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.42    inference(ennf_transformation,[],[f7])).
% 0.20/0.42  fof(f7,axiom,(
% 0.20/0.42    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.20/0.42  fof(f71,plain,(
% 0.20/0.42    ( ! [X1] : (k1_tops_1(X1,u1_struct_0(X1)) = k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),u1_struct_0(X1)))) | ~l1_pre_topc(X1)) )),
% 0.20/0.42    inference(resolution,[],[f45,f56])).
% 0.20/0.42  fof(f56,plain,(
% 0.20/0.42    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.20/0.42    inference(forward_demodulation,[],[f53,f52])).
% 0.20/0.42  fof(f53,plain,(
% 0.20/0.42    ( ! [X0] : (m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0))) )),
% 0.20/0.42    inference(definition_unfolding,[],[f41,f51])).
% 0.20/0.42  fof(f41,plain,(
% 0.20/0.42    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f6])).
% 0.20/0.42  fof(f6,axiom,(
% 0.20/0.42    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.20/0.42  fof(f45,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~l1_pre_topc(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f22])).
% 0.20/0.42  fof(f22,plain,(
% 0.20/0.42    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.42    inference(ennf_transformation,[],[f14])).
% 0.20/0.42  fof(f14,axiom,(
% 0.20/0.42    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).
% 0.20/0.42  % SZS output end Proof for theBenchmark
% 0.20/0.42  % (32631)------------------------------
% 0.20/0.42  % (32631)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (32631)Termination reason: Refutation
% 0.20/0.42  
% 0.20/0.42  % (32631)Memory used [KB]: 1663
% 0.20/0.42  % (32631)Time elapsed: 0.007 s
% 0.20/0.42  % (32631)------------------------------
% 0.20/0.42  % (32631)------------------------------
% 0.20/0.42  % (32618)Success in time 0.064 s
%------------------------------------------------------------------------------
