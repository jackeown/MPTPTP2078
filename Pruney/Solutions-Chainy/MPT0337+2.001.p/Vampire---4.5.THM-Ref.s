%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:39 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   22 (  37 expanded)
%              Number of leaves         :    3 (   8 expanded)
%              Depth                    :   13
%              Number of atoms          :   54 (  98 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f28,plain,(
    $false ),
    inference(subsumption_resolution,[],[f27,f10])).

fof(f10,plain,(
    ~ r1_xboole_0(k3_tarski(sK0),k3_tarski(sK1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ~ r1_xboole_0(k3_tarski(X0),k3_tarski(X1))
      & ! [X2,X3] :
          ( r1_xboole_0(X2,X3)
          | ~ r2_hidden(X3,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1] :
      ( ~ r1_xboole_0(k3_tarski(X0),k3_tarski(X1))
      & ! [X2,X3] :
          ( r1_xboole_0(X2,X3)
          | ~ r2_hidden(X3,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ! [X2,X3] :
            ( ( r2_hidden(X3,X1)
              & r2_hidden(X2,X0) )
           => r1_xboole_0(X2,X3) )
       => r1_xboole_0(k3_tarski(X0),k3_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( r2_hidden(X3,X1)
            & r2_hidden(X2,X0) )
         => r1_xboole_0(X2,X3) )
     => r1_xboole_0(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_zfmisc_1)).

fof(f27,plain,(
    r1_xboole_0(k3_tarski(sK0),k3_tarski(sK1)) ),
    inference(resolution,[],[f26,f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f26,plain,(
    r1_xboole_0(k3_tarski(sK1),k3_tarski(sK0)) ),
    inference(duplicate_literal_removal,[],[f24])).

fof(f24,plain,
    ( r1_xboole_0(k3_tarski(sK1),k3_tarski(sK0))
    | r1_xboole_0(k3_tarski(sK1),k3_tarski(sK0)) ),
    inference(resolution,[],[f22,f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(sK2(X0,X1),X1)
      | r1_xboole_0(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_tarski(X0),X1)
      | ? [X2] :
          ( ~ r1_xboole_0(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_xboole_0(X2,X1) )
     => r1_xboole_0(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_zfmisc_1)).

fof(f22,plain,(
    ! [X0] :
      ( r1_xboole_0(sK2(sK1,X0),k3_tarski(sK0))
      | r1_xboole_0(k3_tarski(sK1),X0) ) ),
    inference(resolution,[],[f21,f11])).

fof(f21,plain,(
    ! [X0] :
      ( r1_xboole_0(k3_tarski(sK0),sK2(sK1,X0))
      | r1_xboole_0(k3_tarski(sK1),X0) ) ),
    inference(duplicate_literal_removal,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( r1_xboole_0(k3_tarski(sK0),sK2(sK1,X0))
      | r1_xboole_0(k3_tarski(sK0),sK2(sK1,X0))
      | r1_xboole_0(k3_tarski(sK1),X0) ) ),
    inference(resolution,[],[f13,f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(sK2(sK0,X0),sK2(sK1,X1))
      | r1_xboole_0(k3_tarski(sK0),X0)
      | r1_xboole_0(k3_tarski(sK1),X1) ) ),
    inference(resolution,[],[f14,f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_xboole_0(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,sK1)
      | r1_xboole_0(k3_tarski(sK0),X0)
      | r1_xboole_0(sK2(sK0,X0),X1) ) ),
    inference(resolution,[],[f12,f9])).

fof(f9,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,sK0)
      | ~ r2_hidden(X3,sK1)
      | r1_xboole_0(X2,X3) ) ),
    inference(cnf_transformation,[],[f6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:51:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (28246)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.22/0.51  % (28256)dis+1011_4_awrs=decay:awrsf=32:afp=40000:afq=1.0:amm=off:anc=all:bs=on:cond=on:fsr=off:gsp=input_only:lma=on:nm=16:nwc=1:nicw=on:sac=on:sp=frequency:thi=all:updr=off:uhcvi=on_670 on theBenchmark
% 0.22/0.51  % (28248)lrs+1003_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=on:fde=unused:gs=on:inw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (28254)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.22/0.51  % (28247)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.22/0.51  % (28246)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(subsumption_resolution,[],[f27,f10])).
% 0.22/0.51  fof(f10,plain,(
% 0.22/0.51    ~r1_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),
% 0.22/0.51    inference(cnf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,plain,(
% 0.22/0.51    ? [X0,X1] : (~r1_xboole_0(k3_tarski(X0),k3_tarski(X1)) & ! [X2,X3] : (r1_xboole_0(X2,X3) | ~r2_hidden(X3,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.51    inference(flattening,[],[f5])).
% 0.22/0.51  fof(f5,plain,(
% 0.22/0.51    ? [X0,X1] : (~r1_xboole_0(k3_tarski(X0),k3_tarski(X1)) & ! [X2,X3] : (r1_xboole_0(X2,X3) | (~r2_hidden(X3,X1) | ~r2_hidden(X2,X0))))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,negated_conjecture,(
% 0.22/0.51    ~! [X0,X1] : (! [X2,X3] : ((r2_hidden(X3,X1) & r2_hidden(X2,X0)) => r1_xboole_0(X2,X3)) => r1_xboole_0(k3_tarski(X0),k3_tarski(X1)))),
% 0.22/0.51    inference(negated_conjecture,[],[f3])).
% 0.22/0.51  fof(f3,conjecture,(
% 0.22/0.51    ! [X0,X1] : (! [X2,X3] : ((r2_hidden(X3,X1) & r2_hidden(X2,X0)) => r1_xboole_0(X2,X3)) => r1_xboole_0(k3_tarski(X0),k3_tarski(X1)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_zfmisc_1)).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    r1_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),
% 0.22/0.51    inference(resolution,[],[f26,f11])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,plain,(
% 0.22/0.51    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    r1_xboole_0(k3_tarski(sK1),k3_tarski(sK0))),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    r1_xboole_0(k3_tarski(sK1),k3_tarski(sK0)) | r1_xboole_0(k3_tarski(sK1),k3_tarski(sK0))),
% 0.22/0.51    inference(resolution,[],[f22,f13])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_xboole_0(sK2(X0,X1),X1) | r1_xboole_0(k3_tarski(X0),X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,plain,(
% 0.22/0.51    ! [X0,X1] : (r1_xboole_0(k3_tarski(X0),X1) | ? [X2] : (~r1_xboole_0(X2,X1) & r2_hidden(X2,X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_xboole_0(X2,X1)) => r1_xboole_0(k3_tarski(X0),X1))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_zfmisc_1)).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ( ! [X0] : (r1_xboole_0(sK2(sK1,X0),k3_tarski(sK0)) | r1_xboole_0(k3_tarski(sK1),X0)) )),
% 0.22/0.51    inference(resolution,[],[f21,f11])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ( ! [X0] : (r1_xboole_0(k3_tarski(sK0),sK2(sK1,X0)) | r1_xboole_0(k3_tarski(sK1),X0)) )),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ( ! [X0] : (r1_xboole_0(k3_tarski(sK0),sK2(sK1,X0)) | r1_xboole_0(k3_tarski(sK0),sK2(sK1,X0)) | r1_xboole_0(k3_tarski(sK1),X0)) )),
% 0.22/0.51    inference(resolution,[],[f13,f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_xboole_0(sK2(sK0,X0),sK2(sK1,X1)) | r1_xboole_0(k3_tarski(sK0),X0) | r1_xboole_0(k3_tarski(sK1),X1)) )),
% 0.22/0.51    inference(resolution,[],[f14,f12])).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_xboole_0(k3_tarski(X0),X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f8])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r2_hidden(X1,sK1) | r1_xboole_0(k3_tarski(sK0),X0) | r1_xboole_0(sK2(sK0,X0),X1)) )),
% 0.22/0.51    inference(resolution,[],[f12,f9])).
% 0.22/0.51  fof(f9,plain,(
% 0.22/0.51    ( ! [X2,X3] : (~r2_hidden(X2,sK0) | ~r2_hidden(X3,sK1) | r1_xboole_0(X2,X3)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f6])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (28246)------------------------------
% 0.22/0.51  % (28246)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (28246)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (28246)Memory used [KB]: 5373
% 0.22/0.51  % (28246)Time elapsed: 0.082 s
% 0.22/0.51  % (28246)------------------------------
% 0.22/0.51  % (28246)------------------------------
% 0.22/0.52  % (28255)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.22/0.52  % (28239)Success in time 0.151 s
%------------------------------------------------------------------------------
