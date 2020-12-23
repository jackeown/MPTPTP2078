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
% DateTime   : Thu Dec  3 13:10:58 EST 2020

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 146 expanded)
%              Number of leaves         :   15 (  41 expanded)
%              Depth                    :   12
%              Number of atoms          :  150 ( 320 expanded)
%              Number of equality atoms :   50 ( 121 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f87,plain,(
    $false ),
    inference(subsumption_resolution,[],[f86,f59])).

fof(f59,plain,(
    u1_struct_0(sK0) != k1_tops_1(sK0,u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f34,f58])).

fof(f58,plain,(
    k2_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(forward_demodulation,[],[f57,f51])).

fof(f51,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f37,f50])).

fof(f50,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f40,f36])).

fof(f36,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(f40,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

fof(f37,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f57,plain,(
    k2_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f56,f54])).

fof(f54,plain,(
    k1_xboole_0 = k1_struct_0(sK0) ),
    inference(resolution,[],[f41,f53])).

fof(f53,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f43,f33])).

fof(f33,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f30])).

fof(f30,plain,
    ( ? [X0] :
        ( k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0))
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).

fof(f43,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f41,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k1_xboole_0 = k1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k1_xboole_0 = k1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_struct_0)).

fof(f56,plain,(
    k2_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k1_struct_0(sK0)) ),
    inference(resolution,[],[f42,f53])).

fof(f42,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k3_subset_1(u1_struct_0(X0),k1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_pre_topc)).

fof(f34,plain,(
    k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f31])).

fof(f86,plain,(
    u1_struct_0(sK0) = k1_tops_1(sK0,u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f85,f51])).

fof(f85,plain,(
    k3_subset_1(u1_struct_0(sK0),k1_xboole_0) = k1_tops_1(sK0,u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f84,f76])).

fof(f76,plain,(
    k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f75,f33])).

fof(f75,plain,
    ( k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f71,f70])).

fof(f70,plain,(
    v4_pre_topc(k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f69,f32])).

fof(f32,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f69,plain,
    ( v4_pre_topc(k1_xboole_0,sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f68,f33])).

fof(f68,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | v4_pre_topc(k1_xboole_0,X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f66,f35])).

fof(f35,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f66,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | v4_pre_topc(k1_xboole_0,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(resolution,[],[f47,f38])).

fof(f38,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_xboole_0(X1)
      | v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
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
         => ( v1_xboole_0(X1)
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).

fof(f71,plain,(
    ! [X0] :
      ( ~ v4_pre_topc(k1_xboole_0,X0)
      | k1_xboole_0 = k2_pre_topc(X0,k1_xboole_0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f45,f38])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f84,plain,(
    k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_xboole_0)) ),
    inference(resolution,[],[f82,f33])).

fof(f82,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(X1)
      | k1_tops_1(X1,u1_struct_0(X1)) = k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f80,f64])).

fof(f64,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) ),
    inference(forward_demodulation,[],[f62,f51])).

fof(f62,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) ),
    inference(resolution,[],[f48,f38])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f80,plain,(
    ! [X1] :
      ( k1_tops_1(X1,u1_struct_0(X1)) = k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),u1_struct_0(X1))))
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f44,f55])).

fof(f55,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f52,f51])).

fof(f52,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f39,f50])).

fof(f39,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f44,plain,(
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
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:10:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.41  % (31356)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.12/0.41  % (31356)Refutation found. Thanks to Tanya!
% 0.12/0.41  % SZS status Theorem for theBenchmark
% 0.12/0.41  % SZS output start Proof for theBenchmark
% 0.12/0.41  fof(f87,plain,(
% 0.12/0.41    $false),
% 0.12/0.41    inference(subsumption_resolution,[],[f86,f59])).
% 0.12/0.41  fof(f59,plain,(
% 0.12/0.41    u1_struct_0(sK0) != k1_tops_1(sK0,u1_struct_0(sK0))),
% 0.12/0.41    inference(backward_demodulation,[],[f34,f58])).
% 0.12/0.41  fof(f58,plain,(
% 0.12/0.41    k2_struct_0(sK0) = u1_struct_0(sK0)),
% 0.12/0.41    inference(forward_demodulation,[],[f57,f51])).
% 0.12/0.42  fof(f51,plain,(
% 0.12/0.42    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 0.12/0.42    inference(definition_unfolding,[],[f37,f50])).
% 0.12/0.42  fof(f50,plain,(
% 0.12/0.42    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 0.12/0.42    inference(definition_unfolding,[],[f40,f36])).
% 0.12/0.42  fof(f36,plain,(
% 0.12/0.42    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 0.12/0.42    inference(cnf_transformation,[],[f2])).
% 0.12/0.42  fof(f2,axiom,(
% 0.12/0.42    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 0.12/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).
% 0.12/0.42  fof(f40,plain,(
% 0.12/0.42    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 0.12/0.42    inference(cnf_transformation,[],[f6])).
% 0.12/0.42  fof(f6,axiom,(
% 0.12/0.42    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 0.12/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).
% 0.12/0.42  fof(f37,plain,(
% 0.12/0.42    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.12/0.42    inference(cnf_transformation,[],[f3])).
% 0.12/0.42  fof(f3,axiom,(
% 0.12/0.42    ! [X0] : k2_subset_1(X0) = X0),
% 0.12/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.12/0.42  fof(f57,plain,(
% 0.12/0.42    k2_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0)),
% 0.12/0.42    inference(forward_demodulation,[],[f56,f54])).
% 0.12/0.42  fof(f54,plain,(
% 0.12/0.42    k1_xboole_0 = k1_struct_0(sK0)),
% 0.12/0.42    inference(resolution,[],[f41,f53])).
% 0.12/0.42  fof(f53,plain,(
% 0.12/0.42    l1_struct_0(sK0)),
% 0.12/0.42    inference(resolution,[],[f43,f33])).
% 0.12/0.42  fof(f33,plain,(
% 0.12/0.42    l1_pre_topc(sK0)),
% 0.12/0.42    inference(cnf_transformation,[],[f31])).
% 0.12/0.42  fof(f31,plain,(
% 0.12/0.42    k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.12/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f30])).
% 0.12/0.42  fof(f30,plain,(
% 0.12/0.42    ? [X0] : (k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.12/0.42    introduced(choice_axiom,[])).
% 0.12/0.42  fof(f18,plain,(
% 0.12/0.42    ? [X0] : (k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.12/0.42    inference(flattening,[],[f17])).
% 0.12/0.42  fof(f17,plain,(
% 0.12/0.42    ? [X0] : (k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0)) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.12/0.42    inference(ennf_transformation,[],[f16])).
% 0.12/0.42  fof(f16,negated_conjecture,(
% 0.12/0.42    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)))),
% 0.12/0.42    inference(negated_conjecture,[],[f15])).
% 0.12/0.42  fof(f15,conjecture,(
% 0.12/0.42    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)))),
% 0.12/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).
% 0.12/0.42  fof(f43,plain,(
% 0.12/0.42    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.12/0.42    inference(cnf_transformation,[],[f21])).
% 0.12/0.42  fof(f21,plain,(
% 0.12/0.42    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.12/0.42    inference(ennf_transformation,[],[f11])).
% 0.12/0.42  fof(f11,axiom,(
% 0.12/0.42    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.12/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.12/0.42  fof(f41,plain,(
% 0.12/0.42    ( ! [X0] : (~l1_struct_0(X0) | k1_xboole_0 = k1_struct_0(X0)) )),
% 0.12/0.42    inference(cnf_transformation,[],[f19])).
% 0.12/0.42  fof(f19,plain,(
% 0.12/0.42    ! [X0] : (k1_xboole_0 = k1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.12/0.42    inference(ennf_transformation,[],[f10])).
% 0.12/0.42  fof(f10,axiom,(
% 0.12/0.42    ! [X0] : (l1_struct_0(X0) => k1_xboole_0 = k1_struct_0(X0))),
% 0.12/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_struct_0)).
% 0.12/0.42  fof(f56,plain,(
% 0.12/0.42    k2_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k1_struct_0(sK0))),
% 0.12/0.42    inference(resolution,[],[f42,f53])).
% 0.12/0.42  fof(f42,plain,(
% 0.12/0.42    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = k3_subset_1(u1_struct_0(X0),k1_struct_0(X0))) )),
% 0.12/0.42    inference(cnf_transformation,[],[f20])).
% 0.12/0.42  fof(f20,plain,(
% 0.12/0.42    ! [X0] : (k2_struct_0(X0) = k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) | ~l1_struct_0(X0))),
% 0.12/0.42    inference(ennf_transformation,[],[f12])).
% 0.12/0.42  fof(f12,axiom,(
% 0.12/0.42    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)))),
% 0.12/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_pre_topc)).
% 0.12/0.42  fof(f34,plain,(
% 0.12/0.42    k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0))),
% 0.12/0.42    inference(cnf_transformation,[],[f31])).
% 0.12/0.42  fof(f86,plain,(
% 0.12/0.42    u1_struct_0(sK0) = k1_tops_1(sK0,u1_struct_0(sK0))),
% 0.12/0.42    inference(forward_demodulation,[],[f85,f51])).
% 0.12/0.42  fof(f85,plain,(
% 0.12/0.42    k3_subset_1(u1_struct_0(sK0),k1_xboole_0) = k1_tops_1(sK0,u1_struct_0(sK0))),
% 0.12/0.42    inference(forward_demodulation,[],[f84,f76])).
% 0.12/0.42  fof(f76,plain,(
% 0.12/0.42    k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0)),
% 0.12/0.42    inference(subsumption_resolution,[],[f75,f33])).
% 0.12/0.42  fof(f75,plain,(
% 0.12/0.42    k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0) | ~l1_pre_topc(sK0)),
% 0.12/0.42    inference(resolution,[],[f71,f70])).
% 0.12/0.42  fof(f70,plain,(
% 0.12/0.42    v4_pre_topc(k1_xboole_0,sK0)),
% 0.12/0.42    inference(subsumption_resolution,[],[f69,f32])).
% 0.12/0.42  fof(f32,plain,(
% 0.12/0.42    v2_pre_topc(sK0)),
% 0.12/0.42    inference(cnf_transformation,[],[f31])).
% 0.12/0.42  fof(f69,plain,(
% 0.12/0.42    v4_pre_topc(k1_xboole_0,sK0) | ~v2_pre_topc(sK0)),
% 0.12/0.42    inference(resolution,[],[f68,f33])).
% 0.12/0.42  fof(f68,plain,(
% 0.12/0.42    ( ! [X0] : (~l1_pre_topc(X0) | v4_pre_topc(k1_xboole_0,X0) | ~v2_pre_topc(X0)) )),
% 0.12/0.42    inference(subsumption_resolution,[],[f66,f35])).
% 0.12/0.42  fof(f35,plain,(
% 0.12/0.42    v1_xboole_0(k1_xboole_0)),
% 0.12/0.42    inference(cnf_transformation,[],[f1])).
% 0.12/0.42  fof(f1,axiom,(
% 0.12/0.42    v1_xboole_0(k1_xboole_0)),
% 0.12/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.12/0.42  fof(f66,plain,(
% 0.12/0.42    ( ! [X0] : (~v1_xboole_0(k1_xboole_0) | v4_pre_topc(k1_xboole_0,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.12/0.42    inference(resolution,[],[f47,f38])).
% 0.12/0.42  fof(f38,plain,(
% 0.12/0.42    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.12/0.42    inference(cnf_transformation,[],[f7])).
% 0.12/0.42  fof(f7,axiom,(
% 0.12/0.42    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.12/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.12/0.42  fof(f47,plain,(
% 0.12/0.42    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1) | v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.12/0.42    inference(cnf_transformation,[],[f26])).
% 0.12/0.42  fof(f26,plain,(
% 0.12/0.42    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.12/0.42    inference(flattening,[],[f25])).
% 0.12/0.42  fof(f25,plain,(
% 0.12/0.42    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.12/0.42    inference(ennf_transformation,[],[f9])).
% 0.12/0.42  fof(f9,axiom,(
% 0.12/0.42    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v4_pre_topc(X1,X0))))),
% 0.12/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).
% 0.12/0.42  fof(f71,plain,(
% 0.12/0.42    ( ! [X0] : (~v4_pre_topc(k1_xboole_0,X0) | k1_xboole_0 = k2_pre_topc(X0,k1_xboole_0) | ~l1_pre_topc(X0)) )),
% 0.12/0.42    inference(resolution,[],[f45,f38])).
% 0.12/0.42  fof(f45,plain,(
% 0.12/0.42    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1 | ~l1_pre_topc(X0)) )),
% 0.12/0.42    inference(cnf_transformation,[],[f24])).
% 0.12/0.42  fof(f24,plain,(
% 0.12/0.42    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.12/0.42    inference(flattening,[],[f23])).
% 0.12/0.42  fof(f23,plain,(
% 0.12/0.42    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.12/0.42    inference(ennf_transformation,[],[f13])).
% 0.12/0.42  fof(f13,axiom,(
% 0.12/0.42    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.12/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.12/0.42  fof(f84,plain,(
% 0.12/0.42    k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_xboole_0))),
% 0.12/0.42    inference(resolution,[],[f82,f33])).
% 0.12/0.42  fof(f82,plain,(
% 0.12/0.42    ( ! [X1] : (~l1_pre_topc(X1) | k1_tops_1(X1,u1_struct_0(X1)) = k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k1_xboole_0))) )),
% 0.12/0.42    inference(forward_demodulation,[],[f80,f64])).
% 0.12/0.42  fof(f64,plain,(
% 0.12/0.42    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,X0)) )),
% 0.12/0.42    inference(forward_demodulation,[],[f62,f51])).
% 0.12/0.42  fof(f62,plain,(
% 0.12/0.42    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0))) )),
% 0.12/0.42    inference(resolution,[],[f48,f38])).
% 0.12/0.42  fof(f48,plain,(
% 0.12/0.42    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.12/0.42    inference(cnf_transformation,[],[f27])).
% 0.12/0.42  fof(f27,plain,(
% 0.12/0.42    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.12/0.42    inference(ennf_transformation,[],[f5])).
% 0.12/0.42  fof(f5,axiom,(
% 0.12/0.42    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.12/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.12/0.42  fof(f80,plain,(
% 0.12/0.42    ( ! [X1] : (k1_tops_1(X1,u1_struct_0(X1)) = k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),u1_struct_0(X1)))) | ~l1_pre_topc(X1)) )),
% 0.12/0.42    inference(resolution,[],[f44,f55])).
% 0.12/0.42  fof(f55,plain,(
% 0.12/0.42    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.12/0.42    inference(forward_demodulation,[],[f52,f51])).
% 0.12/0.42  fof(f52,plain,(
% 0.12/0.42    ( ! [X0] : (m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0))) )),
% 0.12/0.42    inference(definition_unfolding,[],[f39,f50])).
% 0.12/0.42  fof(f39,plain,(
% 0.12/0.42    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.12/0.42    inference(cnf_transformation,[],[f4])).
% 0.12/0.42  fof(f4,axiom,(
% 0.12/0.42    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.12/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.12/0.42  fof(f44,plain,(
% 0.12/0.42    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~l1_pre_topc(X0)) )),
% 0.12/0.42    inference(cnf_transformation,[],[f22])).
% 0.12/0.42  fof(f22,plain,(
% 0.12/0.42    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.12/0.42    inference(ennf_transformation,[],[f14])).
% 0.12/0.42  fof(f14,axiom,(
% 0.12/0.42    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 0.12/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).
% 0.12/0.42  % SZS output end Proof for theBenchmark
% 0.12/0.42  % (31356)------------------------------
% 0.12/0.42  % (31356)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.12/0.42  % (31356)Termination reason: Refutation
% 0.12/0.42  
% 0.12/0.42  % (31356)Memory used [KB]: 1663
% 0.12/0.42  % (31356)Time elapsed: 0.006 s
% 0.12/0.42  % (31356)------------------------------
% 0.12/0.42  % (31356)------------------------------
% 0.19/0.42  % (31343)Success in time 0.064 s
%------------------------------------------------------------------------------
