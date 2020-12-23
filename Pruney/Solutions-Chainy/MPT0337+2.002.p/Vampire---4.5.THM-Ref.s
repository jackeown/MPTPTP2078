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

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   28 (  61 expanded)
%              Number of leaves         :    3 (  12 expanded)
%              Depth                    :   13
%              Number of atoms          :   81 ( 224 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f106,plain,(
    $false ),
    inference(subsumption_resolution,[],[f105,f11])).

fof(f11,plain,(
    ~ r1_xboole_0(k3_tarski(sK0),k3_tarski(sK1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ~ r1_xboole_0(k3_tarski(X0),k3_tarski(X1))
      & ! [X2,X3] :
          ( r1_xboole_0(X2,X3)
          | ~ r2_hidden(X3,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
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

fof(f105,plain,(
    r1_xboole_0(k3_tarski(sK0),k3_tarski(sK1)) ),
    inference(resolution,[],[f104,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0)
      | r1_xboole_0(X1,X0) ) ),
    inference(resolution,[],[f24,f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f24,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(sK2(X3,X4),X5)
      | ~ r1_xboole_0(X4,X5)
      | r1_xboole_0(X3,X4) ) ),
    inference(resolution,[],[f12,f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f12,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f104,plain,(
    r1_xboole_0(k3_tarski(sK1),k3_tarski(sK0)) ),
    inference(duplicate_literal_removal,[],[f102])).

fof(f102,plain,
    ( r1_xboole_0(k3_tarski(sK1),k3_tarski(sK0))
    | r1_xboole_0(k3_tarski(sK1),k3_tarski(sK0)) ),
    inference(resolution,[],[f78,f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(sK3(X0,X1),X1)
      | r1_xboole_0(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
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

fof(f78,plain,(
    ! [X3] :
      ( r1_xboole_0(sK3(sK1,X3),k3_tarski(sK0))
      | r1_xboole_0(k3_tarski(sK1),X3) ) ),
    inference(resolution,[],[f66,f35])).

fof(f35,plain,(
    ! [X2] :
      ( r1_xboole_0(k3_tarski(sK0),sK3(sK1,X2))
      | r1_xboole_0(k3_tarski(sK1),X2) ) ),
    inference(duplicate_literal_removal,[],[f34])).

fof(f34,plain,(
    ! [X2] :
      ( r1_xboole_0(k3_tarski(sK0),sK3(sK1,X2))
      | r1_xboole_0(k3_tarski(sK0),sK3(sK1,X2))
      | r1_xboole_0(k3_tarski(sK1),X2) ) ),
    inference(resolution,[],[f16,f31])).

fof(f31,plain,(
    ! [X4,X5] :
      ( r1_xboole_0(sK3(sK0,X4),sK3(sK1,X5))
      | r1_xboole_0(k3_tarski(sK0),X4)
      | r1_xboole_0(k3_tarski(sK1),X5) ) ),
    inference(resolution,[],[f25,f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_xboole_0(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,sK1)
      | r1_xboole_0(k3_tarski(sK0),X0)
      | r1_xboole_0(sK3(sK0,X0),X1) ) ),
    inference(resolution,[],[f15,f10])).

fof(f10,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,sK0)
      | ~ r2_hidden(X3,sK1)
      | r1_xboole_0(X2,X3) ) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:47:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (17815)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.21/0.47  % (17815)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % (17823)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f106,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(subsumption_resolution,[],[f105,f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ~r1_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),
% 0.21/0.47    inference(cnf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,plain,(
% 0.21/0.47    ? [X0,X1] : (~r1_xboole_0(k3_tarski(X0),k3_tarski(X1)) & ! [X2,X3] : (r1_xboole_0(X2,X3) | ~r2_hidden(X3,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.47    inference(flattening,[],[f6])).
% 0.21/0.47  fof(f6,plain,(
% 0.21/0.47    ? [X0,X1] : (~r1_xboole_0(k3_tarski(X0),k3_tarski(X1)) & ! [X2,X3] : (r1_xboole_0(X2,X3) | (~r2_hidden(X3,X1) | ~r2_hidden(X2,X0))))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1] : (! [X2,X3] : ((r2_hidden(X3,X1) & r2_hidden(X2,X0)) => r1_xboole_0(X2,X3)) => r1_xboole_0(k3_tarski(X0),k3_tarski(X1)))),
% 0.21/0.47    inference(negated_conjecture,[],[f3])).
% 0.21/0.47  fof(f3,conjecture,(
% 0.21/0.47    ! [X0,X1] : (! [X2,X3] : ((r2_hidden(X3,X1) & r2_hidden(X2,X0)) => r1_xboole_0(X2,X3)) => r1_xboole_0(k3_tarski(X0),k3_tarski(X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_zfmisc_1)).
% 0.21/0.47  fof(f105,plain,(
% 0.21/0.47    r1_xboole_0(k3_tarski(sK0),k3_tarski(sK1))),
% 0.21/0.47    inference(resolution,[],[f104,f66])).
% 0.21/0.47  fof(f66,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f63])).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) | r1_xboole_0(X1,X0)) )),
% 0.21/0.47    inference(resolution,[],[f24,f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,plain,(
% 0.21/0.47    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.47    inference(rectify,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ( ! [X4,X5,X3] : (~r2_hidden(sK2(X3,X4),X5) | ~r1_xboole_0(X4,X5) | r1_xboole_0(X3,X4)) )),
% 0.21/0.47    inference(resolution,[],[f12,f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f104,plain,(
% 0.21/0.47    r1_xboole_0(k3_tarski(sK1),k3_tarski(sK0))),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f102])).
% 0.21/0.47  fof(f102,plain,(
% 0.21/0.47    r1_xboole_0(k3_tarski(sK1),k3_tarski(sK0)) | r1_xboole_0(k3_tarski(sK1),k3_tarski(sK0))),
% 0.21/0.47    inference(resolution,[],[f78,f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_xboole_0(sK3(X0,X1),X1) | r1_xboole_0(k3_tarski(X0),X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ! [X0,X1] : (r1_xboole_0(k3_tarski(X0),X1) | ? [X2] : (~r1_xboole_0(X2,X1) & r2_hidden(X2,X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_xboole_0(X2,X1)) => r1_xboole_0(k3_tarski(X0),X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_zfmisc_1)).
% 0.21/0.47  fof(f78,plain,(
% 0.21/0.47    ( ! [X3] : (r1_xboole_0(sK3(sK1,X3),k3_tarski(sK0)) | r1_xboole_0(k3_tarski(sK1),X3)) )),
% 0.21/0.47    inference(resolution,[],[f66,f35])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ( ! [X2] : (r1_xboole_0(k3_tarski(sK0),sK3(sK1,X2)) | r1_xboole_0(k3_tarski(sK1),X2)) )),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ( ! [X2] : (r1_xboole_0(k3_tarski(sK0),sK3(sK1,X2)) | r1_xboole_0(k3_tarski(sK0),sK3(sK1,X2)) | r1_xboole_0(k3_tarski(sK1),X2)) )),
% 0.21/0.47    inference(resolution,[],[f16,f31])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ( ! [X4,X5] : (r1_xboole_0(sK3(sK0,X4),sK3(sK1,X5)) | r1_xboole_0(k3_tarski(sK0),X4) | r1_xboole_0(k3_tarski(sK1),X5)) )),
% 0.21/0.47    inference(resolution,[],[f25,f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_xboole_0(k3_tarski(X0),X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r2_hidden(X1,sK1) | r1_xboole_0(k3_tarski(sK0),X0) | r1_xboole_0(sK3(sK0,X0),X1)) )),
% 0.21/0.47    inference(resolution,[],[f15,f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ( ! [X2,X3] : (~r2_hidden(X2,sK0) | ~r2_hidden(X3,sK1) | r1_xboole_0(X2,X3)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f7])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (17815)------------------------------
% 0.21/0.47  % (17815)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (17815)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (17815)Memory used [KB]: 5373
% 0.21/0.47  % (17815)Time elapsed: 0.055 s
% 0.21/0.47  % (17815)------------------------------
% 0.21/0.47  % (17815)------------------------------
% 0.21/0.48  % (17808)Success in time 0.117 s
%------------------------------------------------------------------------------
