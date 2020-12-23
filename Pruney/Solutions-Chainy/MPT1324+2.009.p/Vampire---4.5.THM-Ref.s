%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:54 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   25 (  41 expanded)
%              Number of leaves         :    4 (   8 expanded)
%              Depth                    :   11
%              Number of atoms          :   63 ( 143 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f27,plain,(
    $false ),
    inference(subsumption_resolution,[],[f26,f15])).

fof(f15,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(X1,k5_setfam_1(u1_struct_0(X0),X2))
              & r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(X1,k5_setfam_1(u1_struct_0(X0),X2))
              & r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ( r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2)))
                 => r1_tarski(X1,k5_setfam_1(u1_struct_0(X0),X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2)))
               => r1_tarski(X1,k5_setfam_1(u1_struct_0(X0),X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_tops_2)).

fof(f26,plain,(
    ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f25,f11])).

fof(f11,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f7])).

fof(f25,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f24,f14])).

fof(f14,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f7])).

fof(f24,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f23,f13])).

fof(f13,plain,(
    ~ r1_tarski(sK1,k5_setfam_1(u1_struct_0(sK0),sK2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f23,plain,
    ( r1_tarski(sK1,k5_setfam_1(u1_struct_0(sK0),sK2))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f20,f16])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2)),k5_setfam_1(u1_struct_0(X0),X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2)),k5_setfam_1(u1_struct_0(X0),X2))
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2)),k5_setfam_1(u1_struct_0(X0),X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_2)).

fof(f20,plain,(
    ! [X0] :
      ( ~ r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2)),X0)
      | r1_tarski(sK1,X0) ) ),
    inference(superposition,[],[f18,f19])).

fof(f19,plain,(
    k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2)) = k2_xboole_0(sK1,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2))) ),
    inference(resolution,[],[f12,f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f12,plain,(
    r1_tarski(sK1,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2))) ),
    inference(cnf_transformation,[],[f7])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:04:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.42  % (27787)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.22/0.42  % (27787)Refutation found. Thanks to Tanya!
% 0.22/0.42  % SZS status Theorem for theBenchmark
% 0.22/0.42  % SZS output start Proof for theBenchmark
% 0.22/0.42  fof(f27,plain,(
% 0.22/0.42    $false),
% 0.22/0.42    inference(subsumption_resolution,[],[f26,f15])).
% 0.22/0.42  fof(f15,plain,(
% 0.22/0.42    l1_pre_topc(sK0)),
% 0.22/0.42    inference(cnf_transformation,[],[f7])).
% 0.22/0.42  fof(f7,plain,(
% 0.22/0.42    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(X1,k5_setfam_1(u1_struct_0(X0),X2)) & r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.22/0.42    inference(flattening,[],[f6])).
% 0.22/0.42  fof(f6,plain,(
% 0.22/0.42    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(X1,k5_setfam_1(u1_struct_0(X0),X2)) & r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.22/0.42    inference(ennf_transformation,[],[f5])).
% 0.22/0.42  fof(f5,negated_conjecture,(
% 0.22/0.42    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2))) => r1_tarski(X1,k5_setfam_1(u1_struct_0(X0),X2))))))),
% 0.22/0.42    inference(negated_conjecture,[],[f4])).
% 0.22/0.42  fof(f4,conjecture,(
% 0.22/0.42    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2))) => r1_tarski(X1,k5_setfam_1(u1_struct_0(X0),X2))))))),
% 0.22/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_tops_2)).
% 0.22/0.42  fof(f26,plain,(
% 0.22/0.42    ~l1_pre_topc(sK0)),
% 0.22/0.42    inference(subsumption_resolution,[],[f25,f11])).
% 0.22/0.42  fof(f11,plain,(
% 0.22/0.42    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.42    inference(cnf_transformation,[],[f7])).
% 0.22/0.42  fof(f25,plain,(
% 0.22/0.42    ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0)),
% 0.22/0.42    inference(subsumption_resolution,[],[f24,f14])).
% 0.22/0.42  fof(f14,plain,(
% 0.22/0.42    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.42    inference(cnf_transformation,[],[f7])).
% 0.22/0.42  fof(f24,plain,(
% 0.22/0.42    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0)),
% 0.22/0.42    inference(subsumption_resolution,[],[f23,f13])).
% 0.22/0.42  fof(f13,plain,(
% 0.22/0.42    ~r1_tarski(sK1,k5_setfam_1(u1_struct_0(sK0),sK2))),
% 0.22/0.42    inference(cnf_transformation,[],[f7])).
% 0.22/0.42  fof(f23,plain,(
% 0.22/0.42    r1_tarski(sK1,k5_setfam_1(u1_struct_0(sK0),sK2)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0)),
% 0.22/0.42    inference(resolution,[],[f20,f16])).
% 0.22/0.42  fof(f16,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2)),k5_setfam_1(u1_struct_0(X0),X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f8])).
% 0.22/0.42  fof(f8,plain,(
% 0.22/0.42    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2)),k5_setfam_1(u1_struct_0(X0),X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.42    inference(ennf_transformation,[],[f3])).
% 0.22/0.42  fof(f3,axiom,(
% 0.22/0.42    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2)),k5_setfam_1(u1_struct_0(X0),X2)))))),
% 0.22/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_2)).
% 0.22/0.42  fof(f20,plain,(
% 0.22/0.42    ( ! [X0] : (~r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2)),X0) | r1_tarski(sK1,X0)) )),
% 0.22/0.42    inference(superposition,[],[f18,f19])).
% 0.22/0.42  fof(f19,plain,(
% 0.22/0.42    k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2)) = k2_xboole_0(sK1,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2)))),
% 0.22/0.42    inference(resolution,[],[f12,f17])).
% 0.22/0.42  fof(f17,plain,(
% 0.22/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.22/0.42    inference(cnf_transformation,[],[f9])).
% 0.22/0.42  fof(f9,plain,(
% 0.22/0.42    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.42    inference(ennf_transformation,[],[f2])).
% 0.22/0.42  fof(f2,axiom,(
% 0.22/0.42    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.22/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.22/0.42  fof(f12,plain,(
% 0.22/0.42    r1_tarski(sK1,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2)))),
% 0.22/0.42    inference(cnf_transformation,[],[f7])).
% 0.22/0.42  fof(f18,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f10])).
% 0.22/0.42  fof(f10,plain,(
% 0.22/0.42    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.22/0.42    inference(ennf_transformation,[],[f1])).
% 0.22/0.42  fof(f1,axiom,(
% 0.22/0.42    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.22/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.22/0.42  % SZS output end Proof for theBenchmark
% 0.22/0.42  % (27787)------------------------------
% 0.22/0.42  % (27787)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.42  % (27787)Termination reason: Refutation
% 0.22/0.42  
% 0.22/0.42  % (27787)Memory used [KB]: 10490
% 0.22/0.42  % (27787)Time elapsed: 0.005 s
% 0.22/0.42  % (27787)------------------------------
% 0.22/0.42  % (27787)------------------------------
% 0.22/0.42  % (27781)Success in time 0.064 s
%------------------------------------------------------------------------------
