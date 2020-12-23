%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:42 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   26 (  40 expanded)
%              Number of leaves         :    4 (   7 expanded)
%              Depth                    :    8
%              Number of atoms          :   66 ( 112 expanded)
%              Number of equality atoms :   13 (  23 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f26,plain,(
    $false ),
    inference(subsumption_resolution,[],[f25,f15])).

fof(f15,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_yellow_1)).

fof(f25,plain,(
    ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f24,f17])).

fof(f17,plain,(
    k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f24,plain,
    ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0)))
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f23,f16])).

fof(f16,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f23,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      | ~ v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f22,f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_pre_topc(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f19,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f19,plain,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => r2_hidden(k1_xboole_0,u1_pre_topc(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_pre_topc)).

fof(f22,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_pre_topc(X0))
      | k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(resolution,[],[f18,f19])).

fof(f18,plain,(
    ! [X0] :
      ( ~ r2_hidden(k1_xboole_0,X0)
      | v1_xboole_0(X0)
      | k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k1_xboole_0,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k1_xboole_0,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k1_xboole_0,X0)
       => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_yellow_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_vampire %s %d
% 0.12/0.31  % Computer   : n010.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.31  % CPULimit   : 60
% 0.17/0.31  % WCLimit    : 600
% 0.17/0.31  % DateTime   : Tue Dec  1 16:08:14 EST 2020
% 0.17/0.32  % CPUTime    : 
% 0.18/0.34  ipcrm: permission denied for id (818282498)
% 0.18/0.34  ipcrm: permission denied for id (818315271)
% 0.18/0.41  ipcrm: permission denied for id (818380860)
% 0.18/0.41  ipcrm: permission denied for id (818413631)
% 0.18/0.42  ipcrm: permission denied for id (818446405)
% 0.18/0.42  ipcrm: permission denied for id (818479178)
% 0.18/0.43  ipcrm: permission denied for id (818511951)
% 0.18/0.55  % (16474)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.18/0.55  % (16474)Refutation found. Thanks to Tanya!
% 0.18/0.55  % SZS status Theorem for theBenchmark
% 0.18/0.55  % SZS output start Proof for theBenchmark
% 0.18/0.55  fof(f26,plain,(
% 0.18/0.55    $false),
% 0.18/0.55    inference(subsumption_resolution,[],[f25,f15])).
% 0.18/0.55  fof(f15,plain,(
% 0.18/0.55    v2_pre_topc(sK0)),
% 0.18/0.55    inference(cnf_transformation,[],[f9])).
% 0.18/0.55  fof(f9,plain,(
% 0.18/0.55    ? [X0] : (k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.18/0.55    inference(flattening,[],[f8])).
% 0.18/0.55  fof(f8,plain,(
% 0.18/0.55    ? [X0] : (k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.18/0.55    inference(ennf_transformation,[],[f7])).
% 0.18/0.55  fof(f7,plain,(
% 0.18/0.55    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 0.18/0.55    inference(pure_predicate_removal,[],[f5])).
% 0.18/0.55  fof(f5,negated_conjecture,(
% 0.18/0.55    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 0.18/0.55    inference(negated_conjecture,[],[f4])).
% 0.18/0.55  fof(f4,conjecture,(
% 0.18/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 0.18/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_yellow_1)).
% 0.18/0.55  fof(f25,plain,(
% 0.18/0.55    ~v2_pre_topc(sK0)),
% 0.18/0.55    inference(subsumption_resolution,[],[f24,f17])).
% 0.18/0.55  fof(f17,plain,(
% 0.18/0.55    k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0)))),
% 0.18/0.55    inference(cnf_transformation,[],[f9])).
% 0.18/0.55  fof(f24,plain,(
% 0.18/0.55    k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) | ~v2_pre_topc(sK0)),
% 0.18/0.55    inference(resolution,[],[f23,f16])).
% 0.18/0.55  fof(f16,plain,(
% 0.18/0.55    l1_pre_topc(sK0)),
% 0.18/0.55    inference(cnf_transformation,[],[f9])).
% 0.18/0.55  fof(f23,plain,(
% 0.18/0.55    ( ! [X0] : (~l1_pre_topc(X0) | k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))) | ~v2_pre_topc(X0)) )),
% 0.18/0.55    inference(subsumption_resolution,[],[f22,f21])).
% 0.18/0.55  fof(f21,plain,(
% 0.18/0.55    ( ! [X0] : (~v1_xboole_0(u1_pre_topc(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 0.18/0.55    inference(resolution,[],[f19,f20])).
% 0.18/0.55  fof(f20,plain,(
% 0.18/0.55    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.18/0.55    inference(cnf_transformation,[],[f14])).
% 0.18/0.55  fof(f14,plain,(
% 0.18/0.55    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 0.18/0.55    inference(ennf_transformation,[],[f6])).
% 0.18/0.55  fof(f6,plain,(
% 0.18/0.55    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 0.18/0.55    inference(unused_predicate_definition_removal,[],[f1])).
% 0.18/0.55  fof(f1,axiom,(
% 0.18/0.55    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.18/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.18/0.55  fof(f19,plain,(
% 0.18/0.55    ( ! [X0] : (r2_hidden(k1_xboole_0,u1_pre_topc(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.18/0.55    inference(cnf_transformation,[],[f13])).
% 0.18/0.55  fof(f13,plain,(
% 0.18/0.55    ! [X0] : (r2_hidden(k1_xboole_0,u1_pre_topc(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.18/0.55    inference(flattening,[],[f12])).
% 0.18/0.55  fof(f12,plain,(
% 0.18/0.55    ! [X0] : (r2_hidden(k1_xboole_0,u1_pre_topc(X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.18/0.55    inference(ennf_transformation,[],[f2])).
% 0.18/0.55  fof(f2,axiom,(
% 0.18/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => r2_hidden(k1_xboole_0,u1_pre_topc(X0)))),
% 0.18/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_pre_topc)).
% 0.18/0.55  fof(f22,plain,(
% 0.18/0.55    ( ! [X0] : (v1_xboole_0(u1_pre_topc(X0)) | k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.18/0.55    inference(resolution,[],[f18,f19])).
% 0.18/0.55  fof(f18,plain,(
% 0.18/0.55    ( ! [X0] : (~r2_hidden(k1_xboole_0,X0) | v1_xboole_0(X0) | k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))) )),
% 0.18/0.55    inference(cnf_transformation,[],[f11])).
% 0.18/0.55  fof(f11,plain,(
% 0.18/0.55    ! [X0] : (k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k1_xboole_0,X0) | v1_xboole_0(X0))),
% 0.18/0.55    inference(flattening,[],[f10])).
% 0.18/0.55  fof(f10,plain,(
% 0.18/0.55    ! [X0] : ((k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k1_xboole_0,X0)) | v1_xboole_0(X0))),
% 0.18/0.55    inference(ennf_transformation,[],[f3])).
% 0.18/0.55  fof(f3,axiom,(
% 0.18/0.55    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k1_xboole_0,X0) => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))))),
% 0.18/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_yellow_1)).
% 0.18/0.55  % SZS output end Proof for theBenchmark
% 0.18/0.55  % (16474)------------------------------
% 0.18/0.55  % (16474)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.55  % (16474)Termination reason: Refutation
% 0.18/0.55  
% 0.18/0.55  % (16474)Memory used [KB]: 10490
% 0.18/0.55  % (16474)Time elapsed: 0.004 s
% 0.18/0.55  % (16474)------------------------------
% 0.18/0.55  % (16474)------------------------------
% 0.18/0.55  % (16340)Success in time 0.221 s
%------------------------------------------------------------------------------
