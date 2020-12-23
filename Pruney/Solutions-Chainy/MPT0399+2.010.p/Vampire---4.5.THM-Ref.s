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
% DateTime   : Thu Dec  3 12:46:08 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   36 (  49 expanded)
%              Number of leaves         :   10 (  15 expanded)
%              Depth                    :   12
%              Number of atoms          :  101 ( 135 expanded)
%              Number of equality atoms :   11 (  20 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f78,plain,(
    $false ),
    inference(resolution,[],[f58,f32])).

fof(f32,plain,(
    v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    v1_xboole_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f3,f21])).

fof(f21,plain,
    ( ? [X0] : v1_xboole_0(X0)
   => v1_xboole_0(sK4) ),
    introduced(choice_axiom,[])).

fof(f3,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

fof(f58,plain,(
    ! [X0] : ~ v1_xboole_0(X0) ),
    inference(subsumption_resolution,[],[f57,f26])).

fof(f26,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK1(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f14])).

fof(f14,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f57,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0,sK1(sK0)),X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f50,f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f50,plain,(
    r2_hidden(sK3(k1_xboole_0,sK1(sK0)),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f49,f24])).

fof(f24,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( k1_xboole_0 != sK0
    & r1_setfam_1(sK0,k1_xboole_0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f10])).

fof(f10,plain,
    ( ? [X0] :
        ( k1_xboole_0 != X0
        & r1_setfam_1(X0,k1_xboole_0) )
   => ( k1_xboole_0 != sK0
      & r1_setfam_1(sK0,k1_xboole_0) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & r1_setfam_1(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( r1_setfam_1(X0,k1_xboole_0)
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( r1_setfam_1(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_setfam_1)).

fof(f49,plain,
    ( r2_hidden(sK3(k1_xboole_0,sK1(sK0)),k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f38,f25])).

fof(f38,plain,
    ( v1_xboole_0(sK0)
    | r2_hidden(sK3(k1_xboole_0,sK1(sK0)),k1_xboole_0) ),
    inference(resolution,[],[f33,f27])).

fof(f27,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK1(X0),X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f33,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | r2_hidden(sK3(k1_xboole_0,X0),k1_xboole_0) ) ),
    inference(resolution,[],[f23,f28])).

fof(f28,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(sK3(X1,X4),X1)
      | ~ r2_hidden(X4,X0)
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f17,f19,f18])).

fof(f18,plain,(
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

fof(f19,plain,(
    ! [X4,X1] :
      ( ? [X5] :
          ( r1_tarski(X4,X5)
          & r2_hidden(X5,X1) )
     => ( r1_tarski(X4,sK3(X1,X4))
        & r2_hidden(sK3(X1,X4),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
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
    inference(rectify,[],[f16])).

fof(f16,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ( ? [X3] :
              ( r1_tarski(X2,X3)
              & r2_hidden(X3,X1) )
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).

fof(f23,plain,(
    r1_setfam_1(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:18:50 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.42  % (1945)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.42  % (1945)Refutation not found, incomplete strategy% (1945)------------------------------
% 0.21/0.42  % (1945)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (1945)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.42  
% 0.21/0.42  % (1945)Memory used [KB]: 6012
% 0.21/0.42  % (1945)Time elapsed: 0.002 s
% 0.21/0.42  % (1945)------------------------------
% 0.21/0.42  % (1945)------------------------------
% 0.21/0.46  % (1947)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % (1938)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.47  % (1938)Refutation not found, incomplete strategy% (1938)------------------------------
% 0.21/0.47  % (1938)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (1938)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (1938)Memory used [KB]: 10490
% 0.21/0.47  % (1938)Time elapsed: 0.061 s
% 0.21/0.47  % (1938)------------------------------
% 0.21/0.47  % (1938)------------------------------
% 0.21/0.48  % (1937)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.48  % (1937)Refutation not found, incomplete strategy% (1937)------------------------------
% 0.21/0.48  % (1937)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (1937)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (1937)Memory used [KB]: 10618
% 0.21/0.48  % (1937)Time elapsed: 0.063 s
% 0.21/0.48  % (1937)------------------------------
% 0.21/0.48  % (1937)------------------------------
% 0.21/0.48  % (1946)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.48  % (1935)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (1946)Refutation not found, incomplete strategy% (1946)------------------------------
% 0.21/0.48  % (1946)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (1946)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (1946)Memory used [KB]: 10490
% 0.21/0.48  % (1946)Time elapsed: 0.072 s
% 0.21/0.48  % (1946)------------------------------
% 0.21/0.48  % (1946)------------------------------
% 0.21/0.48  % (1939)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.48  % (1935)Refutation not found, incomplete strategy% (1935)------------------------------
% 0.21/0.48  % (1935)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (1935)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (1935)Memory used [KB]: 6140
% 0.21/0.48  % (1935)Time elapsed: 0.071 s
% 0.21/0.48  % (1935)------------------------------
% 0.21/0.48  % (1935)------------------------------
% 0.21/0.49  % (1939)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(resolution,[],[f58,f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    v1_xboole_0(sK4)),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    v1_xboole_0(sK4)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f3,f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ? [X0] : v1_xboole_0(X0) => v1_xboole_0(sK4)),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ? [X0] : v1_xboole_0(X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_xboole_0(X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f57,f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK1(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.49    inference(rectify,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.49    inference(nnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    ( ! [X0] : (r2_hidden(sK3(X0,sK1(sK0)),X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.49    inference(superposition,[],[f50,f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    r2_hidden(sK3(k1_xboole_0,sK1(sK0)),k1_xboole_0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f49,f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    k1_xboole_0 != sK0),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    k1_xboole_0 != sK0 & r1_setfam_1(sK0,k1_xboole_0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ? [X0] : (k1_xboole_0 != X0 & r1_setfam_1(X0,k1_xboole_0)) => (k1_xboole_0 != sK0 & r1_setfam_1(sK0,k1_xboole_0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f7,plain,(
% 0.21/0.49    ? [X0] : (k1_xboole_0 != X0 & r1_setfam_1(X0,k1_xboole_0))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,negated_conjecture,(
% 0.21/0.49    ~! [X0] : (r1_setfam_1(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.21/0.49    inference(negated_conjecture,[],[f5])).
% 0.21/0.49  fof(f5,conjecture,(
% 0.21/0.49    ! [X0] : (r1_setfam_1(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_setfam_1)).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    r2_hidden(sK3(k1_xboole_0,sK1(sK0)),k1_xboole_0) | k1_xboole_0 = sK0),
% 0.21/0.49    inference(resolution,[],[f38,f25])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    v1_xboole_0(sK0) | r2_hidden(sK3(k1_xboole_0,sK1(sK0)),k1_xboole_0)),
% 0.21/0.49    inference(resolution,[],[f33,f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK1(X0),X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(sK3(k1_xboole_0,X0),k1_xboole_0)) )),
% 0.21/0.49    inference(resolution,[],[f23,f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ( ! [X4,X0,X1] : (r2_hidden(sK3(X1,X4),X1) | ~r2_hidden(X4,X0) | ~r1_setfam_1(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0,X1] : ((r1_setfam_1(X0,X1) | (! [X3] : (~r1_tarski(sK2(X0,X1),X3) | ~r2_hidden(X3,X1)) & r2_hidden(sK2(X0,X1),X0))) & (! [X4] : ((r1_tarski(X4,sK3(X1,X4)) & r2_hidden(sK3(X1,X4),X1)) | ~r2_hidden(X4,X0)) | ~r1_setfam_1(X0,X1)))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f17,f19,f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X1,X0] : (? [X2] : (! [X3] : (~r1_tarski(X2,X3) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X0)) => (! [X3] : (~r1_tarski(sK2(X0,X1),X3) | ~r2_hidden(X3,X1)) & r2_hidden(sK2(X0,X1),X0)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X4,X1] : (? [X5] : (r1_tarski(X4,X5) & r2_hidden(X5,X1)) => (r1_tarski(X4,sK3(X1,X4)) & r2_hidden(sK3(X1,X4),X1)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0,X1] : ((r1_setfam_1(X0,X1) | ? [X2] : (! [X3] : (~r1_tarski(X2,X3) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X0))) & (! [X4] : (? [X5] : (r1_tarski(X4,X5) & r2_hidden(X5,X1)) | ~r2_hidden(X4,X0)) | ~r1_setfam_1(X0,X1)))),
% 0.21/0.49    inference(rectify,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0,X1] : ((r1_setfam_1(X0,X1) | ? [X2] : (! [X3] : (~r1_tarski(X2,X3) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X0))) & (! [X2] : (? [X3] : (r1_tarski(X2,X3) & r2_hidden(X3,X1)) | ~r2_hidden(X2,X0)) | ~r1_setfam_1(X0,X1)))),
% 0.21/0.49    inference(nnf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ! [X0,X1] : (r1_setfam_1(X0,X1) <=> ! [X2] : (? [X3] : (r1_tarski(X2,X3) & r2_hidden(X3,X1)) | ~r2_hidden(X2,X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : (r1_setfam_1(X0,X1) <=> ! [X2] : ~(! [X3] : ~(r1_tarski(X2,X3) & r2_hidden(X3,X1)) & r2_hidden(X2,X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    r1_setfam_1(sK0,k1_xboole_0)),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (1939)------------------------------
% 0.21/0.49  % (1939)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (1939)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (1939)Memory used [KB]: 1663
% 0.21/0.49  % (1939)Time elapsed: 0.075 s
% 0.21/0.49  % (1939)------------------------------
% 0.21/0.49  % (1939)------------------------------
% 0.21/0.49  % (1940)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (1934)Success in time 0.129 s
%------------------------------------------------------------------------------
