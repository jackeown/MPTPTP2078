%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   45 (  78 expanded)
%              Number of leaves         :   12 (  23 expanded)
%              Depth                    :   13
%              Number of atoms          :  119 ( 191 expanded)
%              Number of equality atoms :   15 (  33 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f83,plain,(
    $false ),
    inference(subsumption_resolution,[],[f80,f28])).

fof(f28,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( k1_xboole_0 != sK0
    & r1_setfam_1(sK0,k1_xboole_0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f17])).

fof(f17,plain,
    ( ? [X0] :
        ( k1_xboole_0 != X0
        & r1_setfam_1(X0,k1_xboole_0) )
   => ( k1_xboole_0 != sK0
      & r1_setfam_1(sK0,k1_xboole_0) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & r1_setfam_1(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( r1_setfam_1(X0,k1_xboole_0)
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( r1_setfam_1(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_setfam_1)).

fof(f80,plain,(
    k1_xboole_0 = sK0 ),
    inference(resolution,[],[f78,f31])).

fof(f31,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f12,f19])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f78,plain,(
    ! [X0] : ~ r2_hidden(X0,sK0) ),
    inference(resolution,[],[f73,f27])).

fof(f27,plain,(
    r1_setfam_1(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f18])).

fof(f73,plain,(
    ! [X2,X1] :
      ( ~ r1_setfam_1(X2,k1_xboole_0)
      | ~ r2_hidden(X1,X2) ) ),
    inference(resolution,[],[f70,f34])).

fof(f34,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(sK3(X1,X4),X1)
      | ~ r2_hidden(X4,X0)
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_setfam_1(X0,X1)
        | ( ! [X3] :
              ( ~ r1_tarski(sK2(X0,X1),X3)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X4] :
            ( ( r1_tarski(X4,sK3(X1,X4))
              & r2_hidden(sK3(X1,X4),X1) )
            | ~ r2_hidden(X4,X0) )
        | ~ r1_setfam_1(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f22,f24,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r1_tarski(X2,X3)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X0) )
     => ( ! [X3] :
            ( ~ r1_tarski(sK2(X0,X1),X3)
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X4,X1] :
      ( ? [X5] :
          ( r1_tarski(X4,X5)
          & r2_hidden(X5,X1) )
     => ( r1_tarski(X4,sK3(X1,X4))
        & r2_hidden(sK3(X1,X4),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_setfam_1(X0,X1)
        | ? [X2] :
            ( ! [X3] :
                ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) )
      & ( ! [X4] :
            ( ? [X5] :
                ( r1_tarski(X4,X5)
                & r2_hidden(X5,X1) )
            | ~ r2_hidden(X4,X0) )
        | ~ r1_setfam_1(X0,X1) ) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_setfam_1(X0,X1)
        | ? [X2] :
            ( ! [X3] :
                ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( ? [X3] :
                ( r1_tarski(X2,X3)
                & r2_hidden(X3,X1) )
            | ~ r2_hidden(X2,X0) )
        | ~ r1_setfam_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ( ? [X3] :
              ( r1_tarski(X2,X3)
              & r2_hidden(X3,X1) )
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

fof(f70,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f68,f27])).

fof(f68,plain,(
    ! [X8,X9] :
      ( ~ r1_setfam_1(X8,k1_xboole_0)
      | ~ r2_hidden(X9,k1_xboole_0) ) ),
    inference(duplicate_literal_removal,[],[f67])).

fof(f67,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(X9,k1_xboole_0)
      | ~ r1_setfam_1(X8,k1_xboole_0)
      | ~ r1_setfam_1(X8,k1_xboole_0) ) ),
    inference(superposition,[],[f54,f57])).

fof(f57,plain,(
    ! [X0] :
      ( k1_xboole_0 = k3_tarski(X0)
      | ~ r1_setfam_1(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f54,f31])).

fof(f54,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(X8,k3_tarski(X9))
      | ~ r1_setfam_1(X9,k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f51,f29])).

fof(f29,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f51,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(X8,k3_tarski(X9))
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ r1_setfam_1(X9,k1_xboole_0) ) ),
    inference(resolution,[],[f47,f44])).

fof(f44,plain,(
    ! [X0] :
      ( r1_tarski(k3_tarski(X0),k1_xboole_0)
      | ~ r1_setfam_1(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f32,f30])).

fof(f30,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_setfam_1)).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | ~ r2_hidden(X1,X2)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f40,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:45:20 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (12436)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.48  % (12436)Refutation not found, incomplete strategy% (12436)------------------------------
% 0.21/0.48  % (12436)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (12436)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (12436)Memory used [KB]: 10490
% 0.21/0.48  % (12436)Time elapsed: 0.050 s
% 0.21/0.48  % (12436)------------------------------
% 0.21/0.48  % (12436)------------------------------
% 0.21/0.48  % (12438)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (12433)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (12451)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.48  % (12451)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(subsumption_resolution,[],[f80,f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    k1_xboole_0 != sK0),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    k1_xboole_0 != sK0 & r1_setfam_1(sK0,k1_xboole_0)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ? [X0] : (k1_xboole_0 != X0 & r1_setfam_1(X0,k1_xboole_0)) => (k1_xboole_0 != sK0 & r1_setfam_1(sK0,k1_xboole_0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ? [X0] : (k1_xboole_0 != X0 & r1_setfam_1(X0,k1_xboole_0))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,negated_conjecture,(
% 0.21/0.48    ~! [X0] : (r1_setfam_1(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.21/0.48    inference(negated_conjecture,[],[f9])).
% 0.21/0.48  fof(f9,conjecture,(
% 0.21/0.48    ! [X0] : (r1_setfam_1(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_setfam_1)).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    k1_xboole_0 = sK0),
% 0.21/0.48    inference(resolution,[],[f78,f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f12,f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(X0,sK0)) )),
% 0.21/0.48    inference(resolution,[],[f73,f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    r1_setfam_1(sK0,k1_xboole_0)),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    ( ! [X2,X1] : (~r1_setfam_1(X2,k1_xboole_0) | ~r2_hidden(X1,X2)) )),
% 0.21/0.48    inference(resolution,[],[f70,f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ( ! [X4,X0,X1] : (r2_hidden(sK3(X1,X4),X1) | ~r2_hidden(X4,X0) | ~r1_setfam_1(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0,X1] : ((r1_setfam_1(X0,X1) | (! [X3] : (~r1_tarski(sK2(X0,X1),X3) | ~r2_hidden(X3,X1)) & r2_hidden(sK2(X0,X1),X0))) & (! [X4] : ((r1_tarski(X4,sK3(X1,X4)) & r2_hidden(sK3(X1,X4),X1)) | ~r2_hidden(X4,X0)) | ~r1_setfam_1(X0,X1)))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f22,f24,f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X1,X0] : (? [X2] : (! [X3] : (~r1_tarski(X2,X3) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X0)) => (! [X3] : (~r1_tarski(sK2(X0,X1),X3) | ~r2_hidden(X3,X1)) & r2_hidden(sK2(X0,X1),X0)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X4,X1] : (? [X5] : (r1_tarski(X4,X5) & r2_hidden(X5,X1)) => (r1_tarski(X4,sK3(X1,X4)) & r2_hidden(sK3(X1,X4),X1)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0,X1] : ((r1_setfam_1(X0,X1) | ? [X2] : (! [X3] : (~r1_tarski(X2,X3) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X0))) & (! [X4] : (? [X5] : (r1_tarski(X4,X5) & r2_hidden(X5,X1)) | ~r2_hidden(X4,X0)) | ~r1_setfam_1(X0,X1)))),
% 0.21/0.48    inference(rectify,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0,X1] : ((r1_setfam_1(X0,X1) | ? [X2] : (! [X3] : (~r1_tarski(X2,X3) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X0))) & (! [X2] : (? [X3] : (r1_tarski(X2,X3) & r2_hidden(X3,X1)) | ~r2_hidden(X2,X0)) | ~r1_setfam_1(X0,X1)))),
% 0.21/0.48    inference(nnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0,X1] : (r1_setfam_1(X0,X1) <=> ! [X2] : (? [X3] : (r1_tarski(X2,X3) & r2_hidden(X3,X1)) | ~r2_hidden(X2,X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1] : (r1_setfam_1(X0,X1) <=> ! [X2] : ~(! [X3] : ~(r1_tarski(X2,X3) & r2_hidden(X3,X1)) & r2_hidden(X2,X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.48    inference(resolution,[],[f68,f27])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    ( ! [X8,X9] : (~r1_setfam_1(X8,k1_xboole_0) | ~r2_hidden(X9,k1_xboole_0)) )),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f67])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    ( ! [X8,X9] : (~r2_hidden(X9,k1_xboole_0) | ~r1_setfam_1(X8,k1_xboole_0) | ~r1_setfam_1(X8,k1_xboole_0)) )),
% 0.21/0.48    inference(superposition,[],[f54,f57])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k3_tarski(X0) | ~r1_setfam_1(X0,k1_xboole_0)) )),
% 0.21/0.48    inference(resolution,[],[f54,f31])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ( ! [X8,X9] : (~r2_hidden(X8,k3_tarski(X9)) | ~r1_setfam_1(X9,k1_xboole_0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f51,f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    v1_xboole_0(k1_xboole_0)),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    v1_xboole_0(k1_xboole_0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    ( ! [X8,X9] : (~r2_hidden(X8,k3_tarski(X9)) | ~v1_xboole_0(k1_xboole_0) | ~r1_setfam_1(X9,k1_xboole_0)) )),
% 0.21/0.48    inference(resolution,[],[f47,f44])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ( ! [X0] : (r1_tarski(k3_tarski(X0),k1_xboole_0) | ~r1_setfam_1(X0,k1_xboole_0)) )),
% 0.21/0.48    inference(superposition,[],[f32,f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.21/0.48    inference(cnf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_setfam_1(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_setfam_1(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1] : (r1_setfam_1(X0,X1) => r1_tarski(k3_tarski(X0),k3_tarski(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_setfam_1)).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | ~r2_hidden(X1,X2) | ~v1_xboole_0(X0)) )),
% 0.21/0.48    inference(resolution,[],[f40,f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.48    inference(nnf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | ~r2_hidden(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (12451)------------------------------
% 0.21/0.48  % (12451)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (12451)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (12451)Memory used [KB]: 1663
% 0.21/0.48  % (12451)Time elapsed: 0.062 s
% 0.21/0.48  % (12451)------------------------------
% 0.21/0.48  % (12451)------------------------------
% 0.21/0.48  % (12440)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  % (12432)Success in time 0.119 s
%------------------------------------------------------------------------------
