%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:42 EST 2020

% Result     : Theorem 1.24s
% Output     : Refutation 1.24s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 159 expanded)
%              Number of leaves         :    8 (  39 expanded)
%              Depth                    :   13
%              Number of atoms          :  118 ( 402 expanded)
%              Number of equality atoms :   10 (  24 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f224,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f173,f139,f134])).

fof(f134,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK4(sK2,k1_zfmisc_1(k2_struct_0(sK0))))
      | r2_hidden(X0,k2_struct_0(sK1)) ) ),
    inference(resolution,[],[f126,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f126,plain,(
    r1_tarski(sK4(sK2,k1_zfmisc_1(k2_struct_0(sK0))),k2_struct_0(sK1)) ),
    inference(unit_resulting_resolution,[],[f69,f123])).

fof(f123,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | r1_tarski(X0,k2_struct_0(sK1)) ) ),
    inference(resolution,[],[f80,f42])).

fof(f42,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
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

fof(f80,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_zfmisc_1(k2_struct_0(sK1)))
      | ~ r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f76,f29])).

fof(f76,plain,(
    r1_tarski(sK2,k1_zfmisc_1(k2_struct_0(sK1))) ),
    inference(unit_resulting_resolution,[],[f57,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f57,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f16,f55])).

fof(f55,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unit_resulting_resolution,[],[f52,f26])).

fof(f26,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f52,plain,(
    l1_struct_0(sK1) ),
    inference(unit_resulting_resolution,[],[f47,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f47,plain,(
    l1_pre_topc(sK1) ),
    inference(unit_resulting_resolution,[],[f19,f18,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f18,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
               => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tops_2)).

fof(f19,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f16,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f10])).

fof(f69,plain,(
    r2_hidden(sK4(sK2,k1_zfmisc_1(k2_struct_0(sK0))),sK2) ),
    inference(unit_resulting_resolution,[],[f68,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f68,plain,(
    ~ r1_tarski(sK2,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f51,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f51,plain,(
    ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0)))) ),
    inference(backward_demodulation,[],[f17,f49])).

fof(f49,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f45,f26])).

fof(f45,plain,(
    l1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f19,f28])).

fof(f17,plain,(
    ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f10])).

fof(f139,plain,(
    r2_hidden(sK4(sK4(sK2,k1_zfmisc_1(k2_struct_0(sK0))),k2_struct_0(sK0)),sK4(sK2,k1_zfmisc_1(k2_struct_0(sK0)))) ),
    inference(unit_resulting_resolution,[],[f137,f30])).

fof(f137,plain,(
    ~ r1_tarski(sK4(sK2,k1_zfmisc_1(k2_struct_0(sK0))),k2_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f70,f43])).

fof(f43,plain,(
    ! [X2,X0] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f70,plain,(
    ~ r2_hidden(sK4(sK2,k1_zfmisc_1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f68,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f173,plain,(
    ~ r2_hidden(sK4(sK4(sK2,k1_zfmisc_1(k2_struct_0(sK0))),k2_struct_0(sK0)),k2_struct_0(sK1)) ),
    inference(unit_resulting_resolution,[],[f137,f131])).

fof(f131,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK4(X1,k2_struct_0(sK0)),k2_struct_0(sK1))
      | r1_tarski(X1,k2_struct_0(sK0)) ) ),
    inference(resolution,[],[f65,f31])).

fof(f65,plain,(
    ! [X1] :
      ( r2_hidden(X1,k2_struct_0(sK0))
      | ~ r2_hidden(X1,k2_struct_0(sK1)) ) ),
    inference(resolution,[],[f53,f29])).

fof(f53,plain,(
    r1_tarski(k2_struct_0(sK1),k2_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f19,f18,f47,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X1)
      | r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_pre_topc)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 21:02:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.50  % (26599)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.50  % (26600)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.51  % (26608)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.52  % (26592)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.52  % (26615)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.52  % (26592)Refutation not found, incomplete strategy% (26592)------------------------------
% 0.22/0.52  % (26592)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (26592)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (26592)Memory used [KB]: 1663
% 0.22/0.52  % (26592)Time elapsed: 0.105 s
% 0.22/0.52  % (26592)------------------------------
% 0.22/0.52  % (26592)------------------------------
% 0.22/0.52  % (26603)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.53  % (26603)Refutation not found, incomplete strategy% (26603)------------------------------
% 0.22/0.53  % (26603)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (26603)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (26603)Memory used [KB]: 10618
% 0.22/0.53  % (26603)Time elapsed: 0.119 s
% 0.22/0.53  % (26603)------------------------------
% 0.22/0.53  % (26603)------------------------------
% 0.22/0.53  % (26604)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (26619)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.53  % (26600)Refutation not found, incomplete strategy% (26600)------------------------------
% 0.22/0.53  % (26600)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (26600)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (26600)Memory used [KB]: 10746
% 0.22/0.53  % (26600)Time elapsed: 0.111 s
% 0.22/0.53  % (26600)------------------------------
% 0.22/0.53  % (26600)------------------------------
% 0.22/0.53  % (26594)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.24/0.54  % (26611)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.24/0.54  % (26595)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.24/0.54  % (26593)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.24/0.54  % (26609)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.24/0.54  % (26596)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.24/0.54  % (26609)Refutation not found, incomplete strategy% (26609)------------------------------
% 1.24/0.54  % (26609)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.54  % (26609)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.54  
% 1.24/0.54  % (26609)Memory used [KB]: 10618
% 1.24/0.54  % (26609)Time elapsed: 0.120 s
% 1.24/0.54  % (26609)------------------------------
% 1.24/0.54  % (26609)------------------------------
% 1.24/0.55  % (26596)Refutation found. Thanks to Tanya!
% 1.24/0.55  % SZS status Theorem for theBenchmark
% 1.24/0.55  % SZS output start Proof for theBenchmark
% 1.24/0.55  fof(f224,plain,(
% 1.24/0.55    $false),
% 1.24/0.55    inference(unit_resulting_resolution,[],[f173,f139,f134])).
% 1.24/0.55  fof(f134,plain,(
% 1.24/0.55    ( ! [X0] : (~r2_hidden(X0,sK4(sK2,k1_zfmisc_1(k2_struct_0(sK0)))) | r2_hidden(X0,k2_struct_0(sK1))) )),
% 1.24/0.55    inference(resolution,[],[f126,f29])).
% 1.24/0.55  fof(f29,plain,(
% 1.24/0.55    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.24/0.55    inference(cnf_transformation,[],[f14])).
% 1.24/0.55  fof(f14,plain,(
% 1.24/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.24/0.55    inference(ennf_transformation,[],[f1])).
% 1.24/0.55  fof(f1,axiom,(
% 1.24/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.24/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.24/0.55  fof(f126,plain,(
% 1.24/0.55    r1_tarski(sK4(sK2,k1_zfmisc_1(k2_struct_0(sK0))),k2_struct_0(sK1))),
% 1.24/0.55    inference(unit_resulting_resolution,[],[f69,f123])).
% 1.24/0.55  fof(f123,plain,(
% 1.24/0.55    ( ! [X0] : (~r2_hidden(X0,sK2) | r1_tarski(X0,k2_struct_0(sK1))) )),
% 1.24/0.55    inference(resolution,[],[f80,f42])).
% 1.24/0.55  fof(f42,plain,(
% 1.24/0.55    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 1.24/0.55    inference(equality_resolution,[],[f23])).
% 1.24/0.55  fof(f23,plain,(
% 1.24/0.55    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.24/0.55    inference(cnf_transformation,[],[f2])).
% 1.24/0.55  fof(f2,axiom,(
% 1.24/0.55    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.24/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.24/0.55  fof(f80,plain,(
% 1.24/0.55    ( ! [X0] : (r2_hidden(X0,k1_zfmisc_1(k2_struct_0(sK1))) | ~r2_hidden(X0,sK2)) )),
% 1.24/0.55    inference(resolution,[],[f76,f29])).
% 1.24/0.55  fof(f76,plain,(
% 1.24/0.55    r1_tarski(sK2,k1_zfmisc_1(k2_struct_0(sK1)))),
% 1.24/0.55    inference(unit_resulting_resolution,[],[f57,f21])).
% 1.24/0.55  fof(f21,plain,(
% 1.24/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.24/0.55    inference(cnf_transformation,[],[f3])).
% 1.24/0.55  fof(f3,axiom,(
% 1.24/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.24/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.24/0.55  fof(f57,plain,(
% 1.24/0.55    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK1))))),
% 1.24/0.55    inference(backward_demodulation,[],[f16,f55])).
% 1.24/0.55  fof(f55,plain,(
% 1.24/0.55    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 1.24/0.55    inference(unit_resulting_resolution,[],[f52,f26])).
% 1.24/0.55  fof(f26,plain,(
% 1.24/0.55    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.24/0.55    inference(cnf_transformation,[],[f11])).
% 1.24/0.55  fof(f11,plain,(
% 1.24/0.55    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.24/0.55    inference(ennf_transformation,[],[f4])).
% 1.24/0.55  fof(f4,axiom,(
% 1.24/0.55    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.24/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 1.24/0.55  fof(f52,plain,(
% 1.24/0.55    l1_struct_0(sK1)),
% 1.24/0.55    inference(unit_resulting_resolution,[],[f47,f28])).
% 1.24/0.55  fof(f28,plain,(
% 1.24/0.55    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 1.24/0.55    inference(cnf_transformation,[],[f13])).
% 1.24/0.55  fof(f13,plain,(
% 1.24/0.55    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.24/0.55    inference(ennf_transformation,[],[f6])).
% 1.24/0.55  fof(f6,axiom,(
% 1.24/0.55    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.24/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.24/0.55  fof(f47,plain,(
% 1.24/0.55    l1_pre_topc(sK1)),
% 1.24/0.55    inference(unit_resulting_resolution,[],[f19,f18,f27])).
% 1.24/0.55  fof(f27,plain,(
% 1.24/0.55    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.24/0.55    inference(cnf_transformation,[],[f12])).
% 1.24/0.55  fof(f12,plain,(
% 1.24/0.55    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.24/0.55    inference(ennf_transformation,[],[f7])).
% 1.24/0.55  fof(f7,axiom,(
% 1.24/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.24/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.24/0.55  fof(f18,plain,(
% 1.24/0.55    m1_pre_topc(sK1,sK0)),
% 1.24/0.55    inference(cnf_transformation,[],[f10])).
% 1.24/0.55  fof(f10,plain,(
% 1.24/0.55    ? [X0] : (? [X1] : (? [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 1.24/0.55    inference(ennf_transformation,[],[f9])).
% 1.24/0.55  fof(f9,negated_conjecture,(
% 1.24/0.55    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))))),
% 1.24/0.55    inference(negated_conjecture,[],[f8])).
% 1.24/0.55  fof(f8,conjecture,(
% 1.24/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))))),
% 1.24/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tops_2)).
% 1.24/0.55  fof(f19,plain,(
% 1.24/0.55    l1_pre_topc(sK0)),
% 1.24/0.55    inference(cnf_transformation,[],[f10])).
% 1.24/0.55  fof(f16,plain,(
% 1.24/0.55    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),
% 1.24/0.55    inference(cnf_transformation,[],[f10])).
% 1.24/0.55  fof(f69,plain,(
% 1.24/0.55    r2_hidden(sK4(sK2,k1_zfmisc_1(k2_struct_0(sK0))),sK2)),
% 1.24/0.55    inference(unit_resulting_resolution,[],[f68,f30])).
% 1.24/0.55  fof(f30,plain,(
% 1.24/0.55    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.24/0.55    inference(cnf_transformation,[],[f14])).
% 1.24/0.55  fof(f68,plain,(
% 1.24/0.55    ~r1_tarski(sK2,k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.24/0.55    inference(unit_resulting_resolution,[],[f51,f20])).
% 1.24/0.55  fof(f20,plain,(
% 1.24/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.24/0.55    inference(cnf_transformation,[],[f3])).
% 1.24/0.55  fof(f51,plain,(
% 1.24/0.55    ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(sK0))))),
% 1.24/0.55    inference(backward_demodulation,[],[f17,f49])).
% 1.24/0.55  fof(f49,plain,(
% 1.24/0.55    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 1.24/0.55    inference(unit_resulting_resolution,[],[f45,f26])).
% 1.24/0.55  fof(f45,plain,(
% 1.24/0.55    l1_struct_0(sK0)),
% 1.24/0.55    inference(unit_resulting_resolution,[],[f19,f28])).
% 1.24/0.55  fof(f17,plain,(
% 1.24/0.55    ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.24/0.55    inference(cnf_transformation,[],[f10])).
% 1.24/0.55  fof(f139,plain,(
% 1.24/0.55    r2_hidden(sK4(sK4(sK2,k1_zfmisc_1(k2_struct_0(sK0))),k2_struct_0(sK0)),sK4(sK2,k1_zfmisc_1(k2_struct_0(sK0))))),
% 1.24/0.55    inference(unit_resulting_resolution,[],[f137,f30])).
% 1.24/0.55  fof(f137,plain,(
% 1.24/0.55    ~r1_tarski(sK4(sK2,k1_zfmisc_1(k2_struct_0(sK0))),k2_struct_0(sK0))),
% 1.24/0.55    inference(unit_resulting_resolution,[],[f70,f43])).
% 1.24/0.55  fof(f43,plain,(
% 1.24/0.55    ( ! [X2,X0] : (~r1_tarski(X2,X0) | r2_hidden(X2,k1_zfmisc_1(X0))) )),
% 1.24/0.55    inference(equality_resolution,[],[f22])).
% 1.24/0.55  fof(f22,plain,(
% 1.24/0.55    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.24/0.55    inference(cnf_transformation,[],[f2])).
% 1.24/0.55  fof(f70,plain,(
% 1.24/0.55    ~r2_hidden(sK4(sK2,k1_zfmisc_1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.24/0.55    inference(unit_resulting_resolution,[],[f68,f31])).
% 1.24/0.55  fof(f31,plain,(
% 1.24/0.55    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.24/0.55    inference(cnf_transformation,[],[f14])).
% 1.24/0.55  fof(f173,plain,(
% 1.24/0.55    ~r2_hidden(sK4(sK4(sK2,k1_zfmisc_1(k2_struct_0(sK0))),k2_struct_0(sK0)),k2_struct_0(sK1))),
% 1.24/0.55    inference(unit_resulting_resolution,[],[f137,f131])).
% 1.24/0.55  fof(f131,plain,(
% 1.24/0.55    ( ! [X1] : (~r2_hidden(sK4(X1,k2_struct_0(sK0)),k2_struct_0(sK1)) | r1_tarski(X1,k2_struct_0(sK0))) )),
% 1.24/0.55    inference(resolution,[],[f65,f31])).
% 1.24/0.55  fof(f65,plain,(
% 1.24/0.55    ( ! [X1] : (r2_hidden(X1,k2_struct_0(sK0)) | ~r2_hidden(X1,k2_struct_0(sK1))) )),
% 1.24/0.55    inference(resolution,[],[f53,f29])).
% 1.24/0.55  fof(f53,plain,(
% 1.24/0.55    r1_tarski(k2_struct_0(sK1),k2_struct_0(sK0))),
% 1.24/0.55    inference(unit_resulting_resolution,[],[f19,f18,f47,f41])).
% 1.24/0.55  fof(f41,plain,(
% 1.24/0.55    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X1) | r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) | ~l1_pre_topc(X0)) )),
% 1.24/0.55    inference(cnf_transformation,[],[f15])).
% 1.24/0.55  fof(f15,plain,(
% 1.24/0.55    ! [X0] : (! [X1] : ((m1_pre_topc(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.24/0.55    inference(ennf_transformation,[],[f5])).
% 1.24/0.55  fof(f5,axiom,(
% 1.24/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))))),
% 1.24/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_pre_topc)).
% 1.24/0.55  % SZS output end Proof for theBenchmark
% 1.24/0.55  % (26596)------------------------------
% 1.24/0.55  % (26596)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.55  % (26596)Termination reason: Refutation
% 1.24/0.55  
% 1.24/0.55  % (26596)Memory used [KB]: 6396
% 1.24/0.55  % (26596)Time elapsed: 0.131 s
% 1.24/0.55  % (26596)------------------------------
% 1.24/0.55  % (26596)------------------------------
% 1.24/0.55  % (26591)Success in time 0.178 s
%------------------------------------------------------------------------------
