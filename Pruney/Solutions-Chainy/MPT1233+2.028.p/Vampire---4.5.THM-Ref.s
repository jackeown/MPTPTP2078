%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:00 EST 2020

% Result     : Theorem 1.50s
% Output     : Refutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 118 expanded)
%              Number of leaves         :   19 (  31 expanded)
%              Depth                    :   12
%              Number of atoms          :  164 ( 247 expanded)
%              Number of equality atoms :   56 (  85 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f256,plain,(
    $false ),
    inference(subsumption_resolution,[],[f255,f94])).

fof(f94,plain,(
    u1_struct_0(sK0) != k1_tops_1(sK0,u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f54,f92])).

fof(f92,plain,(
    k2_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f91,f58])).

fof(f58,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f91,plain,(
    l1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f53,f62])).

fof(f62,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f53,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ? [X0] :
      ( k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0] :
      ( k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f28])).

fof(f28,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).

fof(f54,plain,(
    k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f31])).

fof(f255,plain,(
    u1_struct_0(sK0) = k1_tops_1(sK0,u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f254,f137])).

fof(f137,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f136,f56])).

fof(f56,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f136,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f68,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f68,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f254,plain,(
    k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f253,f162])).

fof(f162,plain,(
    k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f53,f161,f68,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
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

fof(f161,plain,(
    v4_pre_topc(k1_xboole_0,sK0) ),
    inference(unit_resulting_resolution,[],[f52,f53,f83,f68,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_xboole_0(X1)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).

fof(f83,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f52,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f253,plain,(
    k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f251,f144])).

fof(f144,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) ),
    inference(forward_demodulation,[],[f140,f137])).

fof(f140,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f68,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f251,plain,(
    k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(unit_resulting_resolution,[],[f53,f187,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

fof(f187,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f180,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f180,plain,(
    ! [X0] : r2_hidden(X0,k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f153,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_zfmisc_1)).

fof(f153,plain,(
    ! [X0] : ~ r1_xboole_0(k1_tarski(X0),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f86,f75,f90,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).

fof(f90,plain,(
    ! [X1] : k1_xboole_0 != k1_tarski(X1) ),
    inference(forward_demodulation,[],[f88,f89])).

fof(f89,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f84,f56])).

fof(f84,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f67,f79])).

fof(f79,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f67,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f88,plain,(
    ! [X1] : k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f75,plain,(
    ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_zfmisc_1)).

fof(f86,plain,(
    ! [X1] : r1_tarski(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) != X0
      | r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n003.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:57:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (16065)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (16067)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (16072)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.53  % (16073)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.53  % (16065)Refutation not found, incomplete strategy% (16065)------------------------------
% 0.21/0.53  % (16065)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (16065)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (16065)Memory used [KB]: 1663
% 0.21/0.53  % (16065)Time elapsed: 0.109 s
% 0.21/0.53  % (16065)------------------------------
% 0.21/0.53  % (16065)------------------------------
% 0.21/0.54  % (16086)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.54  % (16088)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.54  % (16066)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (16064)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  % (16080)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.54  % (16091)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.54  % (16077)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.54  % (16088)Refutation not found, incomplete strategy% (16088)------------------------------
% 0.21/0.54  % (16088)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (16088)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (16088)Memory used [KB]: 10618
% 0.21/0.54  % (16088)Time elapsed: 0.116 s
% 0.21/0.54  % (16088)------------------------------
% 0.21/0.54  % (16088)------------------------------
% 0.21/0.54  % (16091)Refutation not found, incomplete strategy% (16091)------------------------------
% 0.21/0.54  % (16091)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (16091)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (16091)Memory used [KB]: 6140
% 0.21/0.54  % (16091)Time elapsed: 0.127 s
% 0.21/0.54  % (16091)------------------------------
% 0.21/0.54  % (16091)------------------------------
% 0.21/0.55  % (16080)Refutation not found, incomplete strategy% (16080)------------------------------
% 0.21/0.55  % (16080)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (16080)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (16080)Memory used [KB]: 10618
% 0.21/0.55  % (16080)Time elapsed: 0.117 s
% 0.21/0.55  % (16080)------------------------------
% 0.21/0.55  % (16080)------------------------------
% 0.21/0.55  % (16083)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.55  % (16084)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.50/0.55  % (16079)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.50/0.55  % (16074)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.50/0.55  % (16069)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.50/0.55  % (16081)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.50/0.55  % (16074)Refutation not found, incomplete strategy% (16074)------------------------------
% 1.50/0.55  % (16074)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.55  % (16074)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.55  
% 1.50/0.55  % (16074)Memory used [KB]: 10746
% 1.50/0.55  % (16074)Time elapsed: 0.116 s
% 1.50/0.55  % (16074)------------------------------
% 1.50/0.55  % (16074)------------------------------
% 1.50/0.55  % (16075)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.50/0.56  % (16087)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.50/0.56  % (16093)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.50/0.56  % (16082)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.50/0.56  % (16093)Refutation not found, incomplete strategy% (16093)------------------------------
% 1.50/0.56  % (16093)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.56  % (16093)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.56  
% 1.50/0.56  % (16093)Memory used [KB]: 1663
% 1.50/0.56  % (16093)Time elapsed: 0.002 s
% 1.50/0.56  % (16093)------------------------------
% 1.50/0.56  % (16093)------------------------------
% 1.50/0.56  % (16068)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.50/0.56  % (16070)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.50/0.56  % (16071)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.50/0.56  % (16083)Refutation found. Thanks to Tanya!
% 1.50/0.56  % SZS status Theorem for theBenchmark
% 1.50/0.57  % SZS output start Proof for theBenchmark
% 1.50/0.57  fof(f256,plain,(
% 1.50/0.57    $false),
% 1.50/0.57    inference(subsumption_resolution,[],[f255,f94])).
% 1.50/0.57  fof(f94,plain,(
% 1.50/0.57    u1_struct_0(sK0) != k1_tops_1(sK0,u1_struct_0(sK0))),
% 1.50/0.57    inference(backward_demodulation,[],[f54,f92])).
% 1.50/0.57  fof(f92,plain,(
% 1.50/0.57    k2_struct_0(sK0) = u1_struct_0(sK0)),
% 1.50/0.57    inference(unit_resulting_resolution,[],[f91,f58])).
% 1.50/0.57  fof(f58,plain,(
% 1.50/0.57    ( ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f35])).
% 1.50/0.57  fof(f35,plain,(
% 1.50/0.57    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 1.50/0.57    inference(ennf_transformation,[],[f24])).
% 1.50/0.57  fof(f24,axiom,(
% 1.50/0.57    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 1.50/0.57  fof(f91,plain,(
% 1.50/0.57    l1_struct_0(sK0)),
% 1.50/0.57    inference(unit_resulting_resolution,[],[f53,f62])).
% 1.50/0.57  fof(f62,plain,(
% 1.50/0.57    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f40])).
% 1.50/0.57  fof(f40,plain,(
% 1.50/0.57    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.50/0.57    inference(ennf_transformation,[],[f25])).
% 1.50/0.57  fof(f25,axiom,(
% 1.50/0.57    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.50/0.57  fof(f53,plain,(
% 1.50/0.57    l1_pre_topc(sK0)),
% 1.50/0.57    inference(cnf_transformation,[],[f31])).
% 1.50/0.57  fof(f31,plain,(
% 1.50/0.57    ? [X0] : (k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.50/0.57    inference(flattening,[],[f30])).
% 1.50/0.57  fof(f30,plain,(
% 1.50/0.57    ? [X0] : (k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0)) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.50/0.57    inference(ennf_transformation,[],[f29])).
% 1.50/0.57  fof(f29,negated_conjecture,(
% 1.50/0.57    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)))),
% 1.50/0.57    inference(negated_conjecture,[],[f28])).
% 1.50/0.57  fof(f28,conjecture,(
% 1.50/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)))),
% 1.50/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).
% 1.50/0.57  fof(f54,plain,(
% 1.50/0.57    k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0))),
% 1.50/0.57    inference(cnf_transformation,[],[f31])).
% 1.50/0.57  fof(f255,plain,(
% 1.50/0.57    u1_struct_0(sK0) = k1_tops_1(sK0,u1_struct_0(sK0))),
% 1.50/0.57    inference(forward_demodulation,[],[f254,f137])).
% 1.50/0.57  fof(f137,plain,(
% 1.50/0.57    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 1.50/0.57    inference(forward_demodulation,[],[f136,f56])).
% 1.61/0.57  fof(f56,plain,(
% 1.61/0.57    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.61/0.57    inference(cnf_transformation,[],[f5])).
% 1.61/0.57  fof(f5,axiom,(
% 1.61/0.57    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.61/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.61/0.57  fof(f136,plain,(
% 1.61/0.57    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k3_subset_1(X0,k1_xboole_0)) )),
% 1.61/0.57    inference(unit_resulting_resolution,[],[f68,f78])).
% 1.61/0.57  fof(f78,plain,(
% 1.61/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.61/0.57    inference(cnf_transformation,[],[f47])).
% 1.61/0.57  fof(f47,plain,(
% 1.61/0.57    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.61/0.57    inference(ennf_transformation,[],[f17])).
% 1.61/0.57  fof(f17,axiom,(
% 1.61/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.61/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.61/0.57  fof(f68,plain,(
% 1.61/0.57    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.61/0.57    inference(cnf_transformation,[],[f19])).
% 1.61/0.57  fof(f19,axiom,(
% 1.61/0.57    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.61/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 1.61/0.57  fof(f254,plain,(
% 1.61/0.57    k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0)),
% 1.61/0.57    inference(forward_demodulation,[],[f253,f162])).
% 1.61/0.57  fof(f162,plain,(
% 1.61/0.57    k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0)),
% 1.61/0.57    inference(unit_resulting_resolution,[],[f53,f161,f68,f61])).
% 1.61/0.57  fof(f61,plain,(
% 1.61/0.57    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.61/0.57    inference(cnf_transformation,[],[f39])).
% 1.61/0.57  fof(f39,plain,(
% 1.61/0.57    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.61/0.57    inference(flattening,[],[f38])).
% 1.61/0.57  fof(f38,plain,(
% 1.61/0.57    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.61/0.57    inference(ennf_transformation,[],[f26])).
% 1.61/0.57  fof(f26,axiom,(
% 1.61/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 1.61/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 1.61/0.57  fof(f161,plain,(
% 1.61/0.57    v4_pre_topc(k1_xboole_0,sK0)),
% 1.61/0.57    inference(unit_resulting_resolution,[],[f52,f53,f83,f68,f59])).
% 1.61/0.57  fof(f59,plain,(
% 1.61/0.57    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1) | ~v2_pre_topc(X0)) )),
% 1.61/0.57    inference(cnf_transformation,[],[f37])).
% 1.61/0.57  fof(f37,plain,(
% 1.61/0.57    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.61/0.57    inference(flattening,[],[f36])).
% 1.61/0.57  fof(f36,plain,(
% 1.61/0.57    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.61/0.57    inference(ennf_transformation,[],[f23])).
% 1.61/0.57  fof(f23,axiom,(
% 1.61/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v4_pre_topc(X1,X0))))),
% 1.61/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).
% 1.61/0.57  fof(f83,plain,(
% 1.61/0.57    v1_xboole_0(k1_xboole_0)),
% 1.61/0.57    inference(cnf_transformation,[],[f1])).
% 1.61/0.57  fof(f1,axiom,(
% 1.61/0.57    v1_xboole_0(k1_xboole_0)),
% 1.61/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.61/0.57  fof(f52,plain,(
% 1.61/0.57    v2_pre_topc(sK0)),
% 1.61/0.57    inference(cnf_transformation,[],[f31])).
% 1.61/0.57  fof(f253,plain,(
% 1.61/0.57    k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_xboole_0))),
% 1.61/0.57    inference(forward_demodulation,[],[f251,f144])).
% 1.61/0.57  fof(f144,plain,(
% 1.61/0.57    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,X0)) )),
% 1.61/0.57    inference(forward_demodulation,[],[f140,f137])).
% 1.61/0.57  fof(f140,plain,(
% 1.61/0.57    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0))) )),
% 1.61/0.57    inference(unit_resulting_resolution,[],[f68,f80])).
% 1.61/0.57  fof(f80,plain,(
% 1.61/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 1.61/0.57    inference(cnf_transformation,[],[f48])).
% 1.61/0.57  fof(f48,plain,(
% 1.61/0.57    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.61/0.57    inference(ennf_transformation,[],[f18])).
% 1.61/0.57  fof(f18,axiom,(
% 1.61/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 1.61/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 1.61/0.57  fof(f251,plain,(
% 1.61/0.57    k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))))),
% 1.61/0.57    inference(unit_resulting_resolution,[],[f53,f187,f57])).
% 1.61/0.57  fof(f57,plain,(
% 1.61/0.57    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))) )),
% 1.61/0.57    inference(cnf_transformation,[],[f34])).
% 1.61/0.57  fof(f34,plain,(
% 1.61/0.57    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.61/0.57    inference(ennf_transformation,[],[f27])).
% 1.61/0.57  fof(f27,axiom,(
% 1.61/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 1.61/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).
% 1.61/0.57  fof(f187,plain,(
% 1.61/0.57    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.61/0.57    inference(unit_resulting_resolution,[],[f180,f82])).
% 1.61/0.57  fof(f82,plain,(
% 1.61/0.57    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.61/0.57    inference(cnf_transformation,[],[f51])).
% 1.61/0.57  fof(f51,plain,(
% 1.61/0.57    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.61/0.57    inference(ennf_transformation,[],[f20])).
% 1.61/0.57  fof(f20,axiom,(
% 1.61/0.57    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.61/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 1.61/0.57  fof(f180,plain,(
% 1.61/0.57    ( ! [X0] : (r2_hidden(X0,k1_zfmisc_1(X0))) )),
% 1.61/0.57    inference(unit_resulting_resolution,[],[f153,f73])).
% 1.61/0.57  fof(f73,plain,(
% 1.61/0.57    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.61/0.57    inference(cnf_transformation,[],[f45])).
% 1.61/0.57  fof(f45,plain,(
% 1.61/0.57    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.61/0.57    inference(ennf_transformation,[],[f15])).
% 1.61/0.57  fof(f15,axiom,(
% 1.61/0.57    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.61/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_zfmisc_1)).
% 1.61/0.57  fof(f153,plain,(
% 1.61/0.57    ( ! [X0] : (~r1_xboole_0(k1_tarski(X0),k1_zfmisc_1(X0))) )),
% 1.61/0.57    inference(unit_resulting_resolution,[],[f86,f75,f90,f55])).
% 1.61/0.57  fof(f55,plain,(
% 1.61/0.57    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X0,X2) | ~r1_xboole_0(X1,X2) | k1_xboole_0 = X0) )),
% 1.61/0.57    inference(cnf_transformation,[],[f33])).
% 1.61/0.57  fof(f33,plain,(
% 1.61/0.57    ! [X0,X1,X2] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 1.61/0.57    inference(flattening,[],[f32])).
% 1.61/0.57  fof(f32,plain,(
% 1.61/0.57    ! [X0,X1,X2] : (k1_xboole_0 = X0 | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 1.61/0.57    inference(ennf_transformation,[],[f8])).
% 1.61/0.57  fof(f8,axiom,(
% 1.61/0.57    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k1_xboole_0 = X0)),
% 1.61/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).
% 1.61/0.57  fof(f90,plain,(
% 1.61/0.57    ( ! [X1] : (k1_xboole_0 != k1_tarski(X1)) )),
% 1.61/0.57    inference(forward_demodulation,[],[f88,f89])).
% 1.61/0.57  fof(f89,plain,(
% 1.61/0.57    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.61/0.57    inference(forward_demodulation,[],[f84,f56])).
% 1.61/0.57  fof(f84,plain,(
% 1.61/0.57    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 1.61/0.57    inference(definition_unfolding,[],[f67,f79])).
% 1.61/0.57  fof(f79,plain,(
% 1.61/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.61/0.57    inference(cnf_transformation,[],[f6])).
% 1.61/0.57  fof(f6,axiom,(
% 1.61/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.61/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.61/0.57  fof(f67,plain,(
% 1.61/0.57    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.61/0.57    inference(cnf_transformation,[],[f4])).
% 1.61/0.57  fof(f4,axiom,(
% 1.61/0.57    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.61/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 1.61/0.57  fof(f88,plain,(
% 1.61/0.57    ( ! [X1] : (k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1))) )),
% 1.61/0.57    inference(equality_resolution,[],[f77])).
% 1.61/0.57  fof(f77,plain,(
% 1.61/0.57    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.61/0.57    inference(cnf_transformation,[],[f14])).
% 1.61/0.57  fof(f14,axiom,(
% 1.61/0.57    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 1.61/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 1.61/0.57  fof(f75,plain,(
% 1.61/0.57    ( ! [X0] : (r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0))) )),
% 1.61/0.57    inference(cnf_transformation,[],[f16])).
% 1.61/0.57  fof(f16,axiom,(
% 1.61/0.57    ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0))),
% 1.61/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_zfmisc_1)).
% 1.61/0.57  fof(f86,plain,(
% 1.61/0.57    ( ! [X1] : (r1_tarski(k1_tarski(X1),k1_tarski(X1))) )),
% 1.61/0.57    inference(equality_resolution,[],[f65])).
% 1.61/0.57  fof(f65,plain,(
% 1.61/0.57    ( ! [X0,X1] : (k1_tarski(X1) != X0 | r1_tarski(X0,k1_tarski(X1))) )),
% 1.61/0.57    inference(cnf_transformation,[],[f12])).
% 1.61/0.57  fof(f12,axiom,(
% 1.61/0.57    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.61/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.61/0.57  % SZS output end Proof for theBenchmark
% 1.61/0.57  % (16083)------------------------------
% 1.61/0.57  % (16083)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.57  % (16083)Termination reason: Refutation
% 1.61/0.57  
% 1.61/0.57  % (16083)Memory used [KB]: 1918
% 1.61/0.57  % (16083)Time elapsed: 0.132 s
% 1.61/0.57  % (16083)------------------------------
% 1.61/0.57  % (16083)------------------------------
% 1.61/0.57  % (16063)Success in time 0.199 s
%------------------------------------------------------------------------------
