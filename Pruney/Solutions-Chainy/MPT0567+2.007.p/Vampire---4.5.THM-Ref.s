%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   28 (  38 expanded)
%              Number of leaves         :    8 (  12 expanded)
%              Depth                    :   12
%              Number of atoms          :  115 ( 135 expanded)
%              Number of equality atoms :   18 (  24 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f84,plain,(
    $false ),
    inference(subsumption_resolution,[],[f79,f20])).

fof(f20,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f79,plain,(
    ~ r1_xboole_0(k1_tarski(sK1(sK0,k1_xboole_0,k1_xboole_0)),k1_xboole_0) ),
    inference(resolution,[],[f77,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(f77,plain,(
    r2_hidden(sK1(sK0,k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f74,f20])).

fof(f74,plain,
    ( r2_hidden(sK1(sK0,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ r1_xboole_0(k1_tarski(sK2(sK0,k1_xboole_0,k1_xboole_0)),k1_xboole_0) ),
    inference(resolution,[],[f73,f28])).

fof(f73,plain,
    ( r2_hidden(sK2(sK0,k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | r2_hidden(sK1(sK0,k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X1] :
      ( k1_xboole_0 != X1
      | r2_hidden(sK2(sK0,k1_xboole_0,X1),k1_xboole_0)
      | r2_hidden(sK1(sK0,k1_xboole_0,X1),X1) ) ),
    inference(subsumption_resolution,[],[f39,f18])).

fof(f18,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( k1_xboole_0 != k10_relat_1(sK0,k1_xboole_0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f10])).

fof(f10,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k10_relat_1(X0,k1_xboole_0)
        & v1_relat_1(X0) )
   => ( k1_xboole_0 != k10_relat_1(sK0,k1_xboole_0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( k1_xboole_0 != k10_relat_1(X0,k1_xboole_0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_relat_1)).

fof(f39,plain,(
    ! [X1] :
      ( k1_xboole_0 != X1
      | r2_hidden(sK2(sK0,k1_xboole_0,X1),k1_xboole_0)
      | r2_hidden(sK1(sK0,k1_xboole_0,X1),X1)
      | ~ v1_relat_1(sK0) ) ),
    inference(superposition,[],[f19,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(sK1(X0,X1,X2),X4),X0) )
                | ~ r2_hidden(sK1(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK2(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0) )
                | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ( r2_hidden(sK3(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(X6,sK3(X0,X1,X6)),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f13,f16,f15,f14])).

fof(f14,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X1)
                | ~ r2_hidden(k4_tarski(X3,X4),X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X3,X5),X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X1)
              | ~ r2_hidden(k4_tarski(sK1(X0,X1,X2),X4),X0) )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(sK1(X0,X1,X2),X5),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(sK1(X0,X1,X2),X5),X0) )
     => ( r2_hidden(sK2(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X6,X8),X0) )
     => ( r2_hidden(sK3(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(X6,sK3(X0,X1,X6)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( r2_hidden(X5,X1)
                      & r2_hidden(k4_tarski(X3,X5),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ? [X8] :
                      ( r2_hidden(X8,X1)
                      & r2_hidden(k4_tarski(X6,X8),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X3,X4),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) ) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).

fof(f19,plain,(
    k1_xboole_0 != k10_relat_1(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:56:31 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (27044)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.50  % (27030)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.50  % (27036)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (27030)Refutation not found, incomplete strategy% (27030)------------------------------
% 0.21/0.51  % (27030)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (27030)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (27030)Memory used [KB]: 10618
% 0.21/0.51  % (27030)Time elapsed: 0.059 s
% 0.21/0.51  % (27030)------------------------------
% 0.21/0.51  % (27030)------------------------------
% 0.21/0.51  % (27044)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (27026)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(subsumption_resolution,[],[f79,f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    ~r1_xboole_0(k1_tarski(sK1(sK0,k1_xboole_0,k1_xboole_0)),k1_xboole_0)),
% 0.21/0.51    inference(resolution,[],[f77,f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,plain,(
% 0.21/0.51    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    r2_hidden(sK1(sK0,k1_xboole_0,k1_xboole_0),k1_xboole_0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f74,f20])).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    r2_hidden(sK1(sK0,k1_xboole_0,k1_xboole_0),k1_xboole_0) | ~r1_xboole_0(k1_tarski(sK2(sK0,k1_xboole_0,k1_xboole_0)),k1_xboole_0)),
% 0.21/0.51    inference(resolution,[],[f73,f28])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    r2_hidden(sK2(sK0,k1_xboole_0,k1_xboole_0),k1_xboole_0) | r2_hidden(sK1(sK0,k1_xboole_0,k1_xboole_0),k1_xboole_0)),
% 0.21/0.51    inference(equality_resolution,[],[f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ( ! [X1] : (k1_xboole_0 != X1 | r2_hidden(sK2(sK0,k1_xboole_0,X1),k1_xboole_0) | r2_hidden(sK1(sK0,k1_xboole_0,X1),X1)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f39,f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    v1_relat_1(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    k1_xboole_0 != k10_relat_1(sK0,k1_xboole_0) & v1_relat_1(sK0)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f10])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    ? [X0] : (k1_xboole_0 != k10_relat_1(X0,k1_xboole_0) & v1_relat_1(X0)) => (k1_xboole_0 != k10_relat_1(sK0,k1_xboole_0) & v1_relat_1(sK0))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f7,plain,(
% 0.21/0.51    ? [X0] : (k1_xboole_0 != k10_relat_1(X0,k1_xboole_0) & v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,negated_conjecture,(
% 0.21/0.51    ~! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0))),
% 0.21/0.51    inference(negated_conjecture,[],[f5])).
% 0.21/0.51  fof(f5,conjecture,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_relat_1)).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ( ! [X1] : (k1_xboole_0 != X1 | r2_hidden(sK2(sK0,k1_xboole_0,X1),k1_xboole_0) | r2_hidden(sK1(sK0,k1_xboole_0,X1),X1) | ~v1_relat_1(sK0)) )),
% 0.21/0.51    inference(superposition,[],[f19,f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k10_relat_1(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X2) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK1(X0,X1,X2),X4),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0))) & ((r2_hidden(sK3(X0,X1,X6),X1) & r2_hidden(k4_tarski(X6,sK3(X0,X1,X6)),X0)) | ~r2_hidden(X6,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f13,f16,f15,f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(X3,X2))) => ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK1(X0,X1,X2),X4),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X5),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X2,X1,X0] : (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X5),X0)) => (r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X0)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X6,X1,X0] : (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X6,X8),X0)) => (r2_hidden(sK3(X0,X1,X6),X1) & r2_hidden(k4_tarski(X6,sK3(X0,X1,X6)),X0)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0))) & (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X6,X8),X0)) | ~r2_hidden(X6,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(rectify,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,plain,(
% 0.21/0.51    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    k1_xboole_0 != k10_relat_1(sK0,k1_xboole_0)),
% 0.21/0.51    inference(cnf_transformation,[],[f11])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (27044)------------------------------
% 0.21/0.51  % (27044)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (27044)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (27044)Memory used [KB]: 1791
% 0.21/0.51  % (27044)Time elapsed: 0.063 s
% 0.21/0.51  % (27044)------------------------------
% 0.21/0.51  % (27044)------------------------------
% 0.21/0.51  % (27020)Success in time 0.148 s
%------------------------------------------------------------------------------
