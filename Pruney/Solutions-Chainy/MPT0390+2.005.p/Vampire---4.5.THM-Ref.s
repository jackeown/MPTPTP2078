%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:48 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   27 (  56 expanded)
%              Number of leaves         :    5 (  14 expanded)
%              Depth                    :   10
%              Number of atoms          :   68 ( 169 expanded)
%              Number of equality atoms :    7 (  12 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f39,plain,(
    $false ),
    inference(global_subsumption,[],[f16,f38])).

fof(f38,plain,(
    ~ r1_tarski(sK0,sK2) ),
    inference(backward_demodulation,[],[f17,f32])).

fof(f32,plain,(
    sK0 = k1_setfam_1(sK1) ),
    inference(unit_resulting_resolution,[],[f24,f30,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f30,plain,(
    ~ r2_xboole_0(k1_setfam_1(sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f16,f27,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r2_xboole_0(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r2_xboole_0(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( r2_xboole_0(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r2_xboole_0(X0,X1) )
     => r2_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_xboole_1)).

fof(f27,plain,(
    ~ r2_xboole_0(k1_setfam_1(sK1),sK2) ),
    inference(unit_resulting_resolution,[],[f17,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f24,plain,(
    r1_tarski(k1_setfam_1(sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f15,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

fof(f15,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ~ r1_tarski(k1_setfam_1(sK1),sK2)
    & r1_tarski(sK0,sK2)
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k1_setfam_1(X1),X2)
        & r1_tarski(X0,X2)
        & r2_hidden(X0,X1) )
   => ( ~ r1_tarski(k1_setfam_1(sK1),sK2)
      & r1_tarski(sK0,sK2)
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k1_setfam_1(X1),X2)
      & r1_tarski(X0,X2)
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k1_setfam_1(X1),X2)
      & r1_tarski(X0,X2)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_tarski(X0,X2)
          & r2_hidden(X0,X1) )
       => r1_tarski(k1_setfam_1(X1),X2) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r2_hidden(X0,X1) )
     => r1_tarski(k1_setfam_1(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_setfam_1)).

fof(f17,plain,(
    ~ r1_tarski(k1_setfam_1(sK1),sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f16,plain,(
    r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:49:47 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.47  % (10776)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.48  % (10785)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.48  % (10776)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % (10779)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(global_subsumption,[],[f16,f38])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    ~r1_tarski(sK0,sK2)),
% 0.20/0.48    inference(backward_demodulation,[],[f17,f32])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    sK0 = k1_setfam_1(sK1)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f24,f30,f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.20/0.48    inference(flattening,[],[f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.20/0.48    inference(nnf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    ~r2_xboole_0(k1_setfam_1(sK1),sK0)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f16,f27,f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (r2_xboole_0(X0,X2) | ~r1_tarski(X1,X2) | ~r2_xboole_0(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f10])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (r2_xboole_0(X0,X2) | ~r1_tarski(X1,X2) | ~r2_xboole_0(X0,X1))),
% 0.20/0.48    inference(flattening,[],[f9])).
% 0.20/0.48  fof(f9,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (r2_xboole_0(X0,X2) | (~r1_tarski(X1,X2) | ~r2_xboole_0(X0,X1)))),
% 0.20/0.48    inference(ennf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r2_xboole_0(X0,X1)) => r2_xboole_0(X0,X2))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_xboole_1)).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ~r2_xboole_0(k1_setfam_1(sK1),sK2)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f17,f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    r1_tarski(k1_setfam_1(sK1),sK0)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f15,f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,plain,(
% 0.20/0.48    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    r2_hidden(sK0,sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ~r1_tarski(k1_setfam_1(sK1),sK2) & r1_tarski(sK0,sK2) & r2_hidden(sK0,sK1)),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ? [X0,X1,X2] : (~r1_tarski(k1_setfam_1(X1),X2) & r1_tarski(X0,X2) & r2_hidden(X0,X1)) => (~r1_tarski(k1_setfam_1(sK1),sK2) & r1_tarski(sK0,sK2) & r2_hidden(sK0,sK1))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f7,plain,(
% 0.20/0.48    ? [X0,X1,X2] : (~r1_tarski(k1_setfam_1(X1),X2) & r1_tarski(X0,X2) & r2_hidden(X0,X1))),
% 0.20/0.48    inference(flattening,[],[f6])).
% 0.20/0.48  fof(f6,plain,(
% 0.20/0.48    ? [X0,X1,X2] : (~r1_tarski(k1_setfam_1(X1),X2) & (r1_tarski(X0,X2) & r2_hidden(X0,X1)))),
% 0.20/0.48    inference(ennf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1,X2] : ((r1_tarski(X0,X2) & r2_hidden(X0,X1)) => r1_tarski(k1_setfam_1(X1),X2))),
% 0.20/0.48    inference(negated_conjecture,[],[f4])).
% 0.20/0.48  fof(f4,conjecture,(
% 0.20/0.48    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r2_hidden(X0,X1)) => r1_tarski(k1_setfam_1(X1),X2))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_setfam_1)).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ~r1_tarski(k1_setfam_1(sK1),sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    r1_tarski(sK0,sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (10776)------------------------------
% 0.20/0.48  % (10776)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (10776)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (10776)Memory used [KB]: 10618
% 0.20/0.48  % (10776)Time elapsed: 0.059 s
% 0.20/0.48  % (10776)------------------------------
% 0.20/0.48  % (10776)------------------------------
% 0.20/0.48  % (10760)Success in time 0.124 s
%------------------------------------------------------------------------------
