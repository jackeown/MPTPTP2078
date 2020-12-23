%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:46 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   49 (  76 expanded)
%              Number of leaves         :   11 (  19 expanded)
%              Depth                    :   13
%              Number of atoms          :   97 ( 142 expanded)
%              Number of equality atoms :   15 (  33 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f61,plain,(
    $false ),
    inference(subsumption_resolution,[],[f60,f54])).

fof(f54,plain,(
    ~ r1_tarski(k2_pre_topc(sK0,k2_struct_0(sK0)),k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f53,f22])).

fof(f22,plain,(
    k2_struct_0(sK0) != k2_pre_topc(sK0,k2_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( k2_struct_0(X0) != k2_pre_topc(X0,k2_struct_0(X0))
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_tops_1)).

fof(f53,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k2_struct_0(sK0)),k2_struct_0(sK0))
    | k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0)) ),
    inference(resolution,[],[f49,f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f49,plain,(
    r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f48,f37])).

fof(f37,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f48,plain,(
    r1_tarski(k2_subset_1(k2_struct_0(sK0)),k2_pre_topc(sK0,k2_subset_1(k2_struct_0(sK0)))) ),
    inference(resolution,[],[f46,f35])).

fof(f35,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f46,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | r1_tarski(X0,k2_pre_topc(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f44,f21])).

fof(f21,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f44,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | r1_tarski(X0,k2_pre_topc(sK0,X0)) ) ),
    inference(superposition,[],[f27,f43])).

fof(f43,plain,(
    k2_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(resolution,[],[f42,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f42,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f21,f29])).

fof(f29,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r1_tarski(X1,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

fof(f60,plain,(
    r1_tarski(k2_pre_topc(sK0,k2_struct_0(sK0)),k2_struct_0(sK0)) ),
    inference(resolution,[],[f58,f40])).

fof(f40,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f31])).

% (29353)Refutation not found, incomplete strategy% (29353)------------------------------
% (29353)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (29353)Termination reason: Refutation not found, incomplete strategy

% (29353)Memory used [KB]: 10618
% (29353)Time elapsed: 0.069 s
% (29353)------------------------------
% (29353)------------------------------
fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f58,plain,(
    r2_hidden(k2_pre_topc(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f57,f36])).

fof(f36,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f57,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_struct_0(sK0)))
    | r2_hidden(k2_pre_topc(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(resolution,[],[f51,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f51,plain,(
    m1_subset_1(k2_pre_topc(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f50,f37])).

fof(f50,plain,(
    m1_subset_1(k2_pre_topc(sK0,k2_subset_1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(resolution,[],[f47,f35])).

fof(f47,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | m1_subset_1(k2_pre_topc(sK0,X1),k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f45,f21])).

fof(f45,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | m1_subset_1(k2_pre_topc(sK0,X1),k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(superposition,[],[f26,f43])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.11/0.33  % Computer   : n009.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 17:00:56 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.19/0.45  % (29353)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.19/0.45  % (29358)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.19/0.45  % (29358)Refutation found. Thanks to Tanya!
% 0.19/0.45  % SZS status Theorem for theBenchmark
% 0.19/0.45  % SZS output start Proof for theBenchmark
% 0.19/0.45  fof(f61,plain,(
% 0.19/0.45    $false),
% 0.19/0.45    inference(subsumption_resolution,[],[f60,f54])).
% 0.19/0.45  fof(f54,plain,(
% 0.19/0.45    ~r1_tarski(k2_pre_topc(sK0,k2_struct_0(sK0)),k2_struct_0(sK0))),
% 0.19/0.45    inference(subsumption_resolution,[],[f53,f22])).
% 0.19/0.45  fof(f22,plain,(
% 0.19/0.45    k2_struct_0(sK0) != k2_pre_topc(sK0,k2_struct_0(sK0))),
% 0.19/0.45    inference(cnf_transformation,[],[f13])).
% 0.19/0.45  fof(f13,plain,(
% 0.19/0.45    ? [X0] : (k2_struct_0(X0) != k2_pre_topc(X0,k2_struct_0(X0)) & l1_pre_topc(X0))),
% 0.19/0.45    inference(ennf_transformation,[],[f12])).
% 0.19/0.45  fof(f12,negated_conjecture,(
% 0.19/0.45    ~! [X0] : (l1_pre_topc(X0) => k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)))),
% 0.19/0.45    inference(negated_conjecture,[],[f11])).
% 0.19/0.45  fof(f11,conjecture,(
% 0.19/0.45    ! [X0] : (l1_pre_topc(X0) => k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)))),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_tops_1)).
% 0.19/0.45  fof(f53,plain,(
% 0.19/0.45    ~r1_tarski(k2_pre_topc(sK0,k2_struct_0(sK0)),k2_struct_0(sK0)) | k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0))),
% 0.19/0.45    inference(resolution,[],[f49,f25])).
% 0.19/0.45  fof(f25,plain,(
% 0.19/0.45    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.19/0.45    inference(cnf_transformation,[],[f1])).
% 0.19/0.45  fof(f1,axiom,(
% 0.19/0.45    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.19/0.45  fof(f49,plain,(
% 0.19/0.45    r1_tarski(k2_struct_0(sK0),k2_pre_topc(sK0,k2_struct_0(sK0)))),
% 0.19/0.45    inference(forward_demodulation,[],[f48,f37])).
% 0.19/0.45  fof(f37,plain,(
% 0.19/0.45    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.19/0.45    inference(cnf_transformation,[],[f3])).
% 0.19/0.45  fof(f3,axiom,(
% 0.19/0.45    ! [X0] : k2_subset_1(X0) = X0),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.19/0.45  fof(f48,plain,(
% 0.19/0.45    r1_tarski(k2_subset_1(k2_struct_0(sK0)),k2_pre_topc(sK0,k2_subset_1(k2_struct_0(sK0))))),
% 0.19/0.45    inference(resolution,[],[f46,f35])).
% 0.19/0.45  fof(f35,plain,(
% 0.19/0.45    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.19/0.45    inference(cnf_transformation,[],[f4])).
% 0.19/0.45  fof(f4,axiom,(
% 0.19/0.45    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.19/0.45  fof(f46,plain,(
% 0.19/0.45    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | r1_tarski(X0,k2_pre_topc(sK0,X0))) )),
% 0.19/0.45    inference(subsumption_resolution,[],[f44,f21])).
% 0.19/0.45  fof(f21,plain,(
% 0.19/0.45    l1_pre_topc(sK0)),
% 0.19/0.45    inference(cnf_transformation,[],[f13])).
% 0.19/0.45  fof(f44,plain,(
% 0.19/0.45    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | r1_tarski(X0,k2_pre_topc(sK0,X0))) )),
% 0.19/0.45    inference(superposition,[],[f27,f43])).
% 0.19/0.45  fof(f43,plain,(
% 0.19/0.45    k2_struct_0(sK0) = u1_struct_0(sK0)),
% 0.19/0.45    inference(resolution,[],[f42,f28])).
% 0.19/0.45  fof(f28,plain,(
% 0.19/0.45    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f17])).
% 0.19/0.45  fof(f17,plain,(
% 0.19/0.45    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.19/0.45    inference(ennf_transformation,[],[f7])).
% 0.19/0.45  fof(f7,axiom,(
% 0.19/0.45    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.19/0.45  fof(f42,plain,(
% 0.19/0.45    l1_struct_0(sK0)),
% 0.19/0.45    inference(resolution,[],[f21,f29])).
% 0.19/0.45  fof(f29,plain,(
% 0.19/0.45    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f18])).
% 0.19/0.45  fof(f18,plain,(
% 0.19/0.45    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.19/0.45    inference(ennf_transformation,[],[f9])).
% 0.19/0.45  fof(f9,axiom,(
% 0.19/0.45    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.19/0.45  fof(f27,plain,(
% 0.19/0.45    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | r1_tarski(X1,k2_pre_topc(X0,X1))) )),
% 0.19/0.45    inference(cnf_transformation,[],[f16])).
% 0.19/0.45  fof(f16,plain,(
% 0.19/0.45    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.45    inference(ennf_transformation,[],[f10])).
% 0.19/0.45  fof(f10,axiom,(
% 0.19/0.45    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).
% 0.19/0.45  fof(f60,plain,(
% 0.19/0.45    r1_tarski(k2_pre_topc(sK0,k2_struct_0(sK0)),k2_struct_0(sK0))),
% 0.19/0.45    inference(resolution,[],[f58,f40])).
% 0.19/0.45  fof(f40,plain,(
% 0.19/0.45    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 0.19/0.45    inference(equality_resolution,[],[f31])).
% 0.19/0.45  % (29353)Refutation not found, incomplete strategy% (29353)------------------------------
% 0.19/0.45  % (29353)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.45  % (29353)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.45  
% 0.19/0.45  % (29353)Memory used [KB]: 10618
% 0.19/0.45  % (29353)Time elapsed: 0.069 s
% 0.19/0.45  % (29353)------------------------------
% 0.19/0.45  % (29353)------------------------------
% 0.19/0.45  fof(f31,plain,(
% 0.19/0.45    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.19/0.45    inference(cnf_transformation,[],[f2])).
% 0.19/0.45  fof(f2,axiom,(
% 0.19/0.45    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.19/0.45  fof(f58,plain,(
% 0.19/0.45    r2_hidden(k2_pre_topc(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.19/0.45    inference(subsumption_resolution,[],[f57,f36])).
% 0.19/0.45  fof(f36,plain,(
% 0.19/0.45    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.19/0.45    inference(cnf_transformation,[],[f5])).
% 0.19/0.45  fof(f5,axiom,(
% 0.19/0.45    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.19/0.45  fof(f57,plain,(
% 0.19/0.45    v1_xboole_0(k1_zfmisc_1(k2_struct_0(sK0))) | r2_hidden(k2_pre_topc(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.19/0.45    inference(resolution,[],[f51,f34])).
% 0.19/0.45  fof(f34,plain,(
% 0.19/0.45    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f20])).
% 0.19/0.45  fof(f20,plain,(
% 0.19/0.45    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.19/0.45    inference(flattening,[],[f19])).
% 0.19/0.45  fof(f19,plain,(
% 0.19/0.45    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.19/0.45    inference(ennf_transformation,[],[f6])).
% 0.19/0.45  fof(f6,axiom,(
% 0.19/0.45    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.19/0.45  fof(f51,plain,(
% 0.19/0.45    m1_subset_1(k2_pre_topc(sK0,k2_struct_0(sK0)),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.19/0.45    inference(forward_demodulation,[],[f50,f37])).
% 0.19/0.45  fof(f50,plain,(
% 0.19/0.45    m1_subset_1(k2_pre_topc(sK0,k2_subset_1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.19/0.45    inference(resolution,[],[f47,f35])).
% 0.19/0.45  fof(f47,plain,(
% 0.19/0.45    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | m1_subset_1(k2_pre_topc(sK0,X1),k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 0.19/0.45    inference(subsumption_resolution,[],[f45,f21])).
% 0.19/0.45  fof(f45,plain,(
% 0.19/0.45    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | m1_subset_1(k2_pre_topc(sK0,X1),k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 0.19/0.45    inference(superposition,[],[f26,f43])).
% 0.19/0.45  fof(f26,plain,(
% 0.19/0.45    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.19/0.45    inference(cnf_transformation,[],[f15])).
% 0.19/0.45  fof(f15,plain,(
% 0.19/0.45    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.19/0.45    inference(flattening,[],[f14])).
% 0.19/0.45  fof(f14,plain,(
% 0.19/0.45    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.19/0.45    inference(ennf_transformation,[],[f8])).
% 0.19/0.45  fof(f8,axiom,(
% 0.19/0.45    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.19/0.45  % SZS output end Proof for theBenchmark
% 0.19/0.45  % (29358)------------------------------
% 0.19/0.45  % (29358)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.45  % (29358)Termination reason: Refutation
% 0.19/0.45  
% 0.19/0.45  % (29358)Memory used [KB]: 6140
% 0.19/0.46  % (29358)Time elapsed: 0.066 s
% 0.19/0.46  % (29358)------------------------------
% 0.19/0.46  % (29358)------------------------------
% 0.19/0.46  % (29351)Success in time 0.115 s
%------------------------------------------------------------------------------
