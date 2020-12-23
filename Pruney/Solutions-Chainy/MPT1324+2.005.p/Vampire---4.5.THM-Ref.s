%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:53 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   29 (  45 expanded)
%              Number of leaves         :    5 (   9 expanded)
%              Depth                    :   10
%              Number of atoms          :   73 ( 153 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f77,plain,(
    $false ),
    inference(subsumption_resolution,[],[f76,f14])).

fof(f14,plain,(
    ~ r1_tarski(sK1,k5_setfam_1(u1_struct_0(sK0),sK2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(X1,k5_setfam_1(u1_struct_0(X0),X2))
              & r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(X1,k5_setfam_1(u1_struct_0(X0),X2))
              & r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ( r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2)))
                 => r1_tarski(X1,k5_setfam_1(u1_struct_0(X0),X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2)))
               => r1_tarski(X1,k5_setfam_1(u1_struct_0(X0),X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_tops_2)).

fof(f76,plain,(
    r1_tarski(sK1,k5_setfam_1(u1_struct_0(sK0),sK2)) ),
    inference(resolution,[],[f49,f26])).

fof(f26,plain,(
    r2_hidden(sK1,k1_zfmisc_1(k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2)))) ),
    inference(resolution,[],[f13,f25])).

fof(f25,plain,(
    ! [X2,X0] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f13,plain,(
    r1_tarski(sK1,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2))) ),
    inference(cnf_transformation,[],[f8])).

% (4971)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
fof(f49,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_zfmisc_1(k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2))))
      | r1_tarski(X0,k5_setfam_1(u1_struct_0(sK0),sK2)) ) ),
    inference(resolution,[],[f40,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X1) ) ),
    inference(superposition,[],[f23,f17])).

fof(f17,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k3_tarski(X0),X1)
      | ~ r2_hidden(X2,X0)
      | r1_tarski(X2,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(k3_tarski(X0),X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(k3_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X0)
        & r1_tarski(k3_tarski(X0),X1) )
     => r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_setfam_1)).

fof(f40,plain,(
    r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2)),k5_setfam_1(u1_struct_0(sK0),sK2)) ),
    inference(resolution,[],[f34,f12])).

fof(f12,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f8])).

fof(f34,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,X0)),k5_setfam_1(u1_struct_0(sK0),X0)) ) ),
    inference(subsumption_resolution,[],[f33,f16])).

fof(f16,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f33,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,X0)),k5_setfam_1(u1_struct_0(sK0),X0)) ) ),
    inference(resolution,[],[f18,f15])).

fof(f15,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f8])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2)),k5_setfam_1(u1_struct_0(X0),X2)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2)),k5_setfam_1(u1_struct_0(X0),X2))
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2)),k5_setfam_1(u1_struct_0(X0),X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:29:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.46  % (4976)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.46  % (4976)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % (4963)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.46  % (4967)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f77,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(subsumption_resolution,[],[f76,f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ~r1_tarski(sK1,k5_setfam_1(u1_struct_0(sK0),sK2))),
% 0.20/0.47    inference(cnf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(X1,k5_setfam_1(u1_struct_0(X0),X2)) & r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.20/0.47    inference(flattening,[],[f7])).
% 0.20/0.47  fof(f7,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(X1,k5_setfam_1(u1_struct_0(X0),X2)) & r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,negated_conjecture,(
% 0.20/0.47    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2))) => r1_tarski(X1,k5_setfam_1(u1_struct_0(X0),X2))))))),
% 0.20/0.47    inference(negated_conjecture,[],[f5])).
% 0.20/0.47  fof(f5,conjecture,(
% 0.20/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2))) => r1_tarski(X1,k5_setfam_1(u1_struct_0(X0),X2))))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_tops_2)).
% 0.20/0.47  fof(f76,plain,(
% 0.20/0.47    r1_tarski(sK1,k5_setfam_1(u1_struct_0(sK0),sK2))),
% 0.20/0.47    inference(resolution,[],[f49,f26])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    r2_hidden(sK1,k1_zfmisc_1(k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2))))),
% 0.20/0.47    inference(resolution,[],[f13,f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ( ! [X2,X0] : (~r1_tarski(X2,X0) | r2_hidden(X2,k1_zfmisc_1(X0))) )),
% 0.20/0.47    inference(equality_resolution,[],[f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.20/0.47    inference(cnf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    r1_tarski(sK1,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2)))),
% 0.20/0.47    inference(cnf_transformation,[],[f8])).
% 0.20/0.47  % (4971)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.47  fof(f49,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_hidden(X0,k1_zfmisc_1(k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2)))) | r1_tarski(X0,k5_setfam_1(u1_struct_0(sK0),sK2))) )),
% 0.20/0.47    inference(resolution,[],[f40,f27])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X1)) )),
% 0.20/0.47    inference(superposition,[],[f23,f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r1_tarski(k3_tarski(X0),X1) | ~r2_hidden(X2,X0) | r1_tarski(X2,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f11])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (r1_tarski(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(k3_tarski(X0),X1))),
% 0.20/0.47    inference(flattening,[],[f10])).
% 0.20/0.47  fof(f10,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (r1_tarski(X2,X1) | (~r2_hidden(X2,X0) | ~r1_tarski(k3_tarski(X0),X1)))),
% 0.20/0.47    inference(ennf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : ((r2_hidden(X2,X0) & r1_tarski(k3_tarski(X0),X1)) => r1_tarski(X2,X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_setfam_1)).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2)),k5_setfam_1(u1_struct_0(sK0),sK2))),
% 0.20/0.47    inference(resolution,[],[f34,f12])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.47    inference(cnf_transformation,[],[f8])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,X0)),k5_setfam_1(u1_struct_0(sK0),X0))) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f33,f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    l1_pre_topc(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f8])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,X0)),k5_setfam_1(u1_struct_0(sK0),X0))) )),
% 0.20/0.47    inference(resolution,[],[f18,f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.47    inference(cnf_transformation,[],[f8])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2)),k5_setfam_1(u1_struct_0(X0),X2))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2)),k5_setfam_1(u1_struct_0(X0),X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2)),k5_setfam_1(u1_struct_0(X0),X2)))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_2)).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (4976)------------------------------
% 0.20/0.47  % (4976)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (4976)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (4976)Memory used [KB]: 1663
% 0.20/0.47  % (4976)Time elapsed: 0.051 s
% 0.20/0.47  % (4976)------------------------------
% 0.20/0.47  % (4976)------------------------------
% 0.20/0.47  % (4957)Success in time 0.112 s
%------------------------------------------------------------------------------
