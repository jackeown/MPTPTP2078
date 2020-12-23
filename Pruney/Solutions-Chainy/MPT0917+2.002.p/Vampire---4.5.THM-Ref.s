%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:41 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   22 (  46 expanded)
%              Number of leaves         :    4 (  12 expanded)
%              Depth                    :   11
%              Number of atoms          :   54 ( 152 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22,plain,(
    $false ),
    inference(subsumption_resolution,[],[f21,f11])).

fof(f11,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( ~ r1_tarski(k3_zfmisc_1(sK0,sK2,sK4),k3_zfmisc_1(sK1,sK3,sK5))
    & r1_tarski(sK4,sK5)
    & r1_tarski(sK2,sK3)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f6,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( ~ r1_tarski(k3_zfmisc_1(X0,X2,X4),k3_zfmisc_1(X1,X3,X5))
        & r1_tarski(X4,X5)
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k3_zfmisc_1(sK0,sK2,sK4),k3_zfmisc_1(sK1,sK3,sK5))
      & r1_tarski(sK4,sK5)
      & r1_tarski(sK2,sK3)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k3_zfmisc_1(X0,X2,X4),k3_zfmisc_1(X1,X3,X5))
      & r1_tarski(X4,X5)
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k3_zfmisc_1(X0,X2,X4),k3_zfmisc_1(X1,X3,X5))
      & r1_tarski(X4,X5)
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( ( r1_tarski(X4,X5)
          & r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => r1_tarski(k3_zfmisc_1(X0,X2,X4),k3_zfmisc_1(X1,X3,X5)) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_tarski(X4,X5)
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k3_zfmisc_1(X0,X2,X4),k3_zfmisc_1(X1,X3,X5)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_mcart_1)).

fof(f21,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(subsumption_resolution,[],[f20,f12])).

fof(f12,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f10])).

fof(f20,plain,
    ( ~ r1_tarski(sK2,sK3)
    | ~ r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f19,f16])).

fof(f16,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_zfmisc_1)).

fof(f19,plain,(
    ~ r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)) ),
    inference(subsumption_resolution,[],[f18,f13])).

fof(f13,plain,(
    r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f10])).

fof(f18,plain,
    ( ~ r1_tarski(sK4,sK5)
    | ~ r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)) ),
    inference(resolution,[],[f16,f17])).

fof(f17,plain,(
    ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK2),sK4),k2_zfmisc_1(k2_zfmisc_1(sK1,sK3),sK5)) ),
    inference(definition_unfolding,[],[f14,f15,f15])).

fof(f15,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f14,plain,(
    ~ r1_tarski(k3_zfmisc_1(sK0,sK2,sK4),k3_zfmisc_1(sK1,sK3,sK5)) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n016.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 18:41:04 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.22/0.42  % (19820)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.47  % (19824)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.47  % (19824)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(subsumption_resolution,[],[f21,f11])).
% 0.22/0.47  fof(f11,plain,(
% 0.22/0.47    r1_tarski(sK0,sK1)),
% 0.22/0.47    inference(cnf_transformation,[],[f10])).
% 0.22/0.47  fof(f10,plain,(
% 0.22/0.47    ~r1_tarski(k3_zfmisc_1(sK0,sK2,sK4),k3_zfmisc_1(sK1,sK3,sK5)) & r1_tarski(sK4,sK5) & r1_tarski(sK2,sK3) & r1_tarski(sK0,sK1)),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f6,f9])).
% 0.22/0.47  fof(f9,plain,(
% 0.22/0.47    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k3_zfmisc_1(X0,X2,X4),k3_zfmisc_1(X1,X3,X5)) & r1_tarski(X4,X5) & r1_tarski(X2,X3) & r1_tarski(X0,X1)) => (~r1_tarski(k3_zfmisc_1(sK0,sK2,sK4),k3_zfmisc_1(sK1,sK3,sK5)) & r1_tarski(sK4,sK5) & r1_tarski(sK2,sK3) & r1_tarski(sK0,sK1))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f6,plain,(
% 0.22/0.47    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k3_zfmisc_1(X0,X2,X4),k3_zfmisc_1(X1,X3,X5)) & r1_tarski(X4,X5) & r1_tarski(X2,X3) & r1_tarski(X0,X1))),
% 0.22/0.47    inference(flattening,[],[f5])).
% 0.22/0.47  fof(f5,plain,(
% 0.22/0.47    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k3_zfmisc_1(X0,X2,X4),k3_zfmisc_1(X1,X3,X5)) & (r1_tarski(X4,X5) & r1_tarski(X2,X3) & r1_tarski(X0,X1)))),
% 0.22/0.47    inference(ennf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,negated_conjecture,(
% 0.22/0.47    ~! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X4,X5) & r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k3_zfmisc_1(X0,X2,X4),k3_zfmisc_1(X1,X3,X5)))),
% 0.22/0.47    inference(negated_conjecture,[],[f3])).
% 0.22/0.47  fof(f3,conjecture,(
% 0.22/0.47    ! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X4,X5) & r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k3_zfmisc_1(X0,X2,X4),k3_zfmisc_1(X1,X3,X5)))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_mcart_1)).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    ~r1_tarski(sK0,sK1)),
% 0.22/0.47    inference(subsumption_resolution,[],[f20,f12])).
% 0.22/0.47  fof(f12,plain,(
% 0.22/0.47    r1_tarski(sK2,sK3)),
% 0.22/0.47    inference(cnf_transformation,[],[f10])).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    ~r1_tarski(sK2,sK3) | ~r1_tarski(sK0,sK1)),
% 0.22/0.47    inference(resolution,[],[f19,f16])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    ( ! [X2,X0,X3,X1] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f8])).
% 0.22/0.47  fof(f8,plain,(
% 0.22/0.47    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 0.22/0.47    inference(flattening,[],[f7])).
% 0.22/0.47  fof(f7,plain,(
% 0.22/0.47    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | (~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 0.22/0.47    inference(ennf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_zfmisc_1)).
% 0.22/0.47  fof(f19,plain,(
% 0.22/0.47    ~r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))),
% 0.22/0.47    inference(subsumption_resolution,[],[f18,f13])).
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    r1_tarski(sK4,sK5)),
% 0.22/0.47    inference(cnf_transformation,[],[f10])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    ~r1_tarski(sK4,sK5) | ~r1_tarski(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))),
% 0.22/0.47    inference(resolution,[],[f16,f17])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    ~r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK2),sK4),k2_zfmisc_1(k2_zfmisc_1(sK1,sK3),sK5))),
% 0.22/0.47    inference(definition_unfolding,[],[f14,f15,f15])).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    ~r1_tarski(k3_zfmisc_1(sK0,sK2,sK4),k3_zfmisc_1(sK1,sK3,sK5))),
% 0.22/0.47    inference(cnf_transformation,[],[f10])).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (19824)------------------------------
% 0.22/0.47  % (19824)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (19824)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (19824)Memory used [KB]: 6012
% 0.22/0.47  % (19824)Time elapsed: 0.004 s
% 0.22/0.47  % (19824)------------------------------
% 0.22/0.47  % (19824)------------------------------
% 0.22/0.48  % (19816)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.48  % (19818)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.48  % (19809)Success in time 0.107 s
%------------------------------------------------------------------------------
