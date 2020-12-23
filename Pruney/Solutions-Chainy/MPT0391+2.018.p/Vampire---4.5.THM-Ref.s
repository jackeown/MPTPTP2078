%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:51 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   39 (  66 expanded)
%              Number of leaves         :    7 (  17 expanded)
%              Depth                    :   11
%              Number of atoms          :  101 ( 213 expanded)
%              Number of equality atoms :   10 (  17 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f119,plain,(
    $false ),
    inference(global_subsumption,[],[f20,f118])).

fof(f118,plain,(
    r1_xboole_0(k1_setfam_1(sK1),sK2) ),
    inference(superposition,[],[f66,f51])).

fof(f51,plain,(
    sK2 = k4_xboole_0(sK2,sK0) ),
    inference(resolution,[],[f47,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f47,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(resolution,[],[f40,f19])).

fof(f19,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ~ r1_xboole_0(k1_setfam_1(sK1),sK2)
    & r1_xboole_0(sK0,sK2)
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(k1_setfam_1(X1),X2)
        & r1_xboole_0(X0,X2)
        & r2_hidden(X0,X1) )
   => ( ~ r1_xboole_0(k1_setfam_1(sK1),sK2)
      & r1_xboole_0(sK0,sK2)
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k1_setfam_1(X1),X2)
      & r1_xboole_0(X0,X2)
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k1_setfam_1(X1),X2)
      & r1_xboole_0(X0,X2)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X0,X2)
          & r2_hidden(X0,X1) )
       => r1_xboole_0(k1_setfam_1(X1),X2) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r2_hidden(X0,X1) )
     => r1_xboole_0(k1_setfam_1(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_setfam_1)).

fof(f40,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(X2,X3)
      | r1_xboole_0(X3,X2) ) ),
    inference(duplicate_literal_removal,[],[f39])).

fof(f39,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(X2,X3)
      | r1_xboole_0(X3,X2)
      | r1_xboole_0(X3,X2) ) ),
    inference(resolution,[],[f34,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f10,f15])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f34,plain,(
    ! [X2,X3,X1] :
      ( ~ r2_hidden(sK3(X2,X3),X1)
      | ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X2,X3) ) ),
    inference(resolution,[],[f23,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f66,plain,(
    ! [X4] : r1_xboole_0(k1_setfam_1(sK1),k4_xboole_0(X4,sK0)) ),
    inference(trivial_inequality_removal,[],[f65])).

fof(f65,plain,(
    ! [X4] :
      ( k1_setfam_1(sK1) != k1_setfam_1(sK1)
      | r1_xboole_0(k1_setfam_1(sK1),k4_xboole_0(X4,sK0)) ) ),
    inference(superposition,[],[f26,f53])).

fof(f53,plain,(
    ! [X0] : k1_setfam_1(sK1) = k4_xboole_0(k1_setfam_1(sK1),k4_xboole_0(X0,sK0)) ),
    inference(resolution,[],[f37,f18])).

fof(f18,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | k1_setfam_1(X0) = k4_xboole_0(k1_setfam_1(X0),k4_xboole_0(X1,X2)) ) ),
    inference(resolution,[],[f31,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,k4_xboole_0(X2,X1)) = X0 ) ),
    inference(resolution,[],[f27,f25])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f20,plain,(
    ~ r1_xboole_0(k1_setfam_1(sK1),sK2) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:25:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.42  % (27891)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.21/0.43  % (27885)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.43  % (27891)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f119,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(global_subsumption,[],[f20,f118])).
% 0.21/0.43  fof(f118,plain,(
% 0.21/0.43    r1_xboole_0(k1_setfam_1(sK1),sK2)),
% 0.21/0.43    inference(superposition,[],[f66,f51])).
% 0.21/0.43  fof(f51,plain,(
% 0.21/0.43    sK2 = k4_xboole_0(sK2,sK0)),
% 0.21/0.43    inference(resolution,[],[f47,f25])).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 0.21/0.43    inference(cnf_transformation,[],[f17])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.43    inference(nnf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.43  fof(f47,plain,(
% 0.21/0.43    r1_xboole_0(sK2,sK0)),
% 0.21/0.43    inference(resolution,[],[f40,f19])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    r1_xboole_0(sK0,sK2)),
% 0.21/0.43    inference(cnf_transformation,[],[f14])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    ~r1_xboole_0(k1_setfam_1(sK1),sK2) & r1_xboole_0(sK0,sK2) & r2_hidden(sK0,sK1)),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f13])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    ? [X0,X1,X2] : (~r1_xboole_0(k1_setfam_1(X1),X2) & r1_xboole_0(X0,X2) & r2_hidden(X0,X1)) => (~r1_xboole_0(k1_setfam_1(sK1),sK2) & r1_xboole_0(sK0,sK2) & r2_hidden(sK0,sK1))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f9,plain,(
% 0.21/0.43    ? [X0,X1,X2] : (~r1_xboole_0(k1_setfam_1(X1),X2) & r1_xboole_0(X0,X2) & r2_hidden(X0,X1))),
% 0.21/0.43    inference(flattening,[],[f8])).
% 0.21/0.43  fof(f8,plain,(
% 0.21/0.43    ? [X0,X1,X2] : (~r1_xboole_0(k1_setfam_1(X1),X2) & (r1_xboole_0(X0,X2) & r2_hidden(X0,X1)))),
% 0.21/0.43    inference(ennf_transformation,[],[f6])).
% 0.21/0.43  fof(f6,negated_conjecture,(
% 0.21/0.43    ~! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r2_hidden(X0,X1)) => r1_xboole_0(k1_setfam_1(X1),X2))),
% 0.21/0.43    inference(negated_conjecture,[],[f5])).
% 0.21/0.43  fof(f5,conjecture,(
% 0.21/0.43    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r2_hidden(X0,X1)) => r1_xboole_0(k1_setfam_1(X1),X2))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_setfam_1)).
% 0.21/0.43  fof(f40,plain,(
% 0.21/0.43    ( ! [X2,X3] : (~r1_xboole_0(X2,X3) | r1_xboole_0(X3,X2)) )),
% 0.21/0.43    inference(duplicate_literal_removal,[],[f39])).
% 0.21/0.43  fof(f39,plain,(
% 0.21/0.43    ( ! [X2,X3] : (~r1_xboole_0(X2,X3) | r1_xboole_0(X3,X2) | r1_xboole_0(X3,X2)) )),
% 0.21/0.43    inference(resolution,[],[f34,f22])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f16])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f10,f15])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.43    inference(ennf_transformation,[],[f7])).
% 0.21/0.43  fof(f7,plain,(
% 0.21/0.43    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.43    inference(rectify,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.43  fof(f34,plain,(
% 0.21/0.43    ( ! [X2,X3,X1] : (~r2_hidden(sK3(X2,X3),X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X2,X3)) )),
% 0.21/0.43    inference(resolution,[],[f23,f21])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f16])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f16])).
% 0.21/0.43  fof(f66,plain,(
% 0.21/0.43    ( ! [X4] : (r1_xboole_0(k1_setfam_1(sK1),k4_xboole_0(X4,sK0))) )),
% 0.21/0.43    inference(trivial_inequality_removal,[],[f65])).
% 0.21/0.43  fof(f65,plain,(
% 0.21/0.43    ( ! [X4] : (k1_setfam_1(sK1) != k1_setfam_1(sK1) | r1_xboole_0(k1_setfam_1(sK1),k4_xboole_0(X4,sK0))) )),
% 0.21/0.43    inference(superposition,[],[f26,f53])).
% 0.21/0.43  fof(f53,plain,(
% 0.21/0.43    ( ! [X0] : (k1_setfam_1(sK1) = k4_xboole_0(k1_setfam_1(sK1),k4_xboole_0(X0,sK0))) )),
% 0.21/0.43    inference(resolution,[],[f37,f18])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    r2_hidden(sK0,sK1)),
% 0.21/0.43    inference(cnf_transformation,[],[f14])).
% 0.21/0.43  fof(f37,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | k1_setfam_1(X0) = k4_xboole_0(k1_setfam_1(X0),k4_xboole_0(X1,X2))) )),
% 0.21/0.43    inference(resolution,[],[f31,f24])).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f11])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,axiom,(
% 0.21/0.43    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).
% 0.21/0.43  fof(f31,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X2,X1)) = X0) )),
% 0.21/0.43    inference(resolution,[],[f27,f25])).
% 0.21/0.43  fof(f27,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f12])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).
% 0.21/0.43  fof(f26,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f17])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    ~r1_xboole_0(k1_setfam_1(sK1),sK2)),
% 0.21/0.43    inference(cnf_transformation,[],[f14])).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (27891)------------------------------
% 0.21/0.43  % (27891)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (27891)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (27891)Memory used [KB]: 10618
% 0.21/0.43  % (27891)Time elapsed: 0.009 s
% 0.21/0.43  % (27891)------------------------------
% 0.21/0.43  % (27891)------------------------------
% 0.21/0.43  % (27879)Success in time 0.075 s
%------------------------------------------------------------------------------
