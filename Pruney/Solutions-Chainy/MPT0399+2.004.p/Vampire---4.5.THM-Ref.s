%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:07 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   38 (  43 expanded)
%              Number of leaves         :   10 (  12 expanded)
%              Depth                    :   10
%              Number of atoms          :   97 ( 109 expanded)
%              Number of equality atoms :   13 (  19 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f52,plain,(
    $false ),
    inference(subsumption_resolution,[],[f50,f25])).

fof(f25,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( k1_xboole_0 != sK0
    & r1_setfam_1(sK0,k1_xboole_0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f16])).

fof(f16,plain,
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
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( r1_setfam_1(X0,k1_xboole_0)
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( r1_setfam_1(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_setfam_1)).

fof(f50,plain,(
    k1_xboole_0 = sK0 ),
    inference(resolution,[],[f49,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0))
        & ~ r1_tarski(X0,k2_zfmisc_1(X0,X1)) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k2_zfmisc_1(X1,X0))
        | r1_tarski(X0,k2_zfmisc_1(X0,X1)) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t135_zfmisc_1)).

fof(f49,plain,(
    ! [X2] : r1_tarski(sK0,X2) ),
    inference(subsumption_resolution,[],[f47,f36])).

fof(f36,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f26,f27])).

fof(f27,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(f26,plain,(
    ! [X0] : v1_xboole_0(k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : v1_xboole_0(k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc13_subset_1)).

fof(f47,plain,(
    ! [X2] :
      ( r1_tarski(sK0,X2)
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[],[f45,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f45,plain,(
    ! [X0] :
      ( r2_hidden(sK2(k1_xboole_0,sK1(sK0,X0)),k1_xboole_0)
      | r1_tarski(sK0,X0) ) ),
    inference(resolution,[],[f44,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f44,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | r2_hidden(sK2(k1_xboole_0,X0),k1_xboole_0) ) ),
    inference(resolution,[],[f34,f24])).

fof(f24,plain,(
    r1_setfam_1(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f17])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_setfam_1(X0,X1)
      | ~ r2_hidden(X2,X0)
      | r2_hidden(sK2(X1,X2),X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X2,sK2(X1,X2))
            & r2_hidden(sK2(X1,X2),X1) )
          | ~ r2_hidden(X2,X0) )
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f22])).

fof(f22,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( r1_tarski(X2,X3)
          & r2_hidden(X3,X1) )
     => ( r1_tarski(X2,sK2(X1,X2))
        & r2_hidden(sK2(X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ? [X3] :
              ( r1_tarski(X2,X3)
              & r2_hidden(X3,X1) )
          | ~ r2_hidden(X2,X0) )
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
     => ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    inference(unused_predicate_definition_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:45:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.52  % (13253)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.54  % (13266)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.54  % (13258)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.54  % (13247)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.54  % (13243)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.54  % (13247)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  fof(f52,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(subsumption_resolution,[],[f50,f25])).
% 0.20/0.54  fof(f25,plain,(
% 0.20/0.54    k1_xboole_0 != sK0),
% 0.20/0.54    inference(cnf_transformation,[],[f17])).
% 0.20/0.54  fof(f17,plain,(
% 0.20/0.54    k1_xboole_0 != sK0 & r1_setfam_1(sK0,k1_xboole_0)),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f16])).
% 0.20/0.54  fof(f16,plain,(
% 0.20/0.54    ? [X0] : (k1_xboole_0 != X0 & r1_setfam_1(X0,k1_xboole_0)) => (k1_xboole_0 != sK0 & r1_setfam_1(sK0,k1_xboole_0))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f11,plain,(
% 0.20/0.54    ? [X0] : (k1_xboole_0 != X0 & r1_setfam_1(X0,k1_xboole_0))),
% 0.20/0.54    inference(ennf_transformation,[],[f8])).
% 0.20/0.54  fof(f8,negated_conjecture,(
% 0.20/0.54    ~! [X0] : (r1_setfam_1(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.20/0.54    inference(negated_conjecture,[],[f7])).
% 0.20/0.54  fof(f7,conjecture,(
% 0.20/0.54    ! [X0] : (r1_setfam_1(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_setfam_1)).
% 0.20/0.54  fof(f50,plain,(
% 0.20/0.54    k1_xboole_0 = sK0),
% 0.20/0.54    inference(resolution,[],[f49,f29])).
% 0.20/0.54  fof(f29,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X0,X1)) | k1_xboole_0 = X0) )),
% 0.20/0.54    inference(cnf_transformation,[],[f13])).
% 0.20/0.54  fof(f13,plain,(
% 0.20/0.54    ! [X0,X1] : (k1_xboole_0 = X0 | (~r1_tarski(X0,k2_zfmisc_1(X1,X0)) & ~r1_tarski(X0,k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(ennf_transformation,[],[f3])).
% 0.20/0.54  fof(f3,axiom,(
% 0.20/0.54    ! [X0,X1] : ((r1_tarski(X0,k2_zfmisc_1(X1,X0)) | r1_tarski(X0,k2_zfmisc_1(X0,X1))) => k1_xboole_0 = X0)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t135_zfmisc_1)).
% 0.20/0.54  fof(f49,plain,(
% 0.20/0.54    ( ! [X2] : (r1_tarski(sK0,X2)) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f47,f36])).
% 0.20/0.54  fof(f36,plain,(
% 0.20/0.54    v1_xboole_0(k1_xboole_0)),
% 0.20/0.54    inference(backward_demodulation,[],[f26,f27])).
% 0.20/0.54  fof(f27,plain,(
% 0.20/0.54    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f4])).
% 0.20/0.54  fof(f4,axiom,(
% 0.20/0.54    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).
% 0.20/0.54  fof(f26,plain,(
% 0.20/0.54    ( ! [X0] : (v1_xboole_0(k1_subset_1(X0))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f5])).
% 0.20/0.54  fof(f5,axiom,(
% 0.20/0.54    ! [X0] : v1_xboole_0(k1_subset_1(X0))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc13_subset_1)).
% 0.20/0.54  fof(f47,plain,(
% 0.20/0.54    ( ! [X2] : (r1_tarski(sK0,X2) | ~v1_xboole_0(k1_xboole_0)) )),
% 0.20/0.54    inference(resolution,[],[f45,f28])).
% 0.20/0.54  fof(f28,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f12])).
% 0.20/0.54  fof(f12,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f10])).
% 0.20/0.54  fof(f10,plain,(
% 0.20/0.54    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.54    inference(unused_predicate_definition_removal,[],[f1])).
% 0.20/0.54  fof(f1,axiom,(
% 0.20/0.54    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.54  fof(f45,plain,(
% 0.20/0.54    ( ! [X0] : (r2_hidden(sK2(k1_xboole_0,sK1(sK0,X0)),k1_xboole_0) | r1_tarski(sK0,X0)) )),
% 0.20/0.54    inference(resolution,[],[f44,f32])).
% 0.20/0.54  fof(f32,plain,(
% 0.20/0.54    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f21])).
% 0.20/0.54  fof(f21,plain,(
% 0.20/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f20])).
% 0.20/0.54  fof(f20,plain,(
% 0.20/0.54    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f19,plain,(
% 0.20/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.54    inference(rectify,[],[f18])).
% 0.20/0.54  fof(f18,plain,(
% 0.20/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.54    inference(nnf_transformation,[],[f14])).
% 0.20/0.54  fof(f14,plain,(
% 0.20/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f2])).
% 0.20/0.54  fof(f2,axiom,(
% 0.20/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.54  fof(f44,plain,(
% 0.20/0.54    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(sK2(k1_xboole_0,X0),k1_xboole_0)) )),
% 0.20/0.54    inference(resolution,[],[f34,f24])).
% 0.20/0.54  fof(f24,plain,(
% 0.20/0.54    r1_setfam_1(sK0,k1_xboole_0)),
% 0.20/0.54    inference(cnf_transformation,[],[f17])).
% 0.20/0.54  fof(f34,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~r1_setfam_1(X0,X1) | ~r2_hidden(X2,X0) | r2_hidden(sK2(X1,X2),X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f23])).
% 0.20/0.54  fof(f23,plain,(
% 0.20/0.54    ! [X0,X1] : (! [X2] : ((r1_tarski(X2,sK2(X1,X2)) & r2_hidden(sK2(X1,X2),X1)) | ~r2_hidden(X2,X0)) | ~r1_setfam_1(X0,X1))),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f22])).
% 0.20/0.54  fof(f22,plain,(
% 0.20/0.54    ! [X2,X1] : (? [X3] : (r1_tarski(X2,X3) & r2_hidden(X3,X1)) => (r1_tarski(X2,sK2(X1,X2)) & r2_hidden(sK2(X1,X2),X1)))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f15,plain,(
% 0.20/0.54    ! [X0,X1] : (! [X2] : (? [X3] : (r1_tarski(X2,X3) & r2_hidden(X3,X1)) | ~r2_hidden(X2,X0)) | ~r1_setfam_1(X0,X1))),
% 0.20/0.54    inference(ennf_transformation,[],[f9])).
% 0.20/0.54  fof(f9,plain,(
% 0.20/0.54    ! [X0,X1] : (r1_setfam_1(X0,X1) => ! [X2] : ~(! [X3] : ~(r1_tarski(X2,X3) & r2_hidden(X3,X1)) & r2_hidden(X2,X0)))),
% 0.20/0.54    inference(unused_predicate_definition_removal,[],[f6])).
% 0.20/0.54  fof(f6,axiom,(
% 0.20/0.54    ! [X0,X1] : (r1_setfam_1(X0,X1) <=> ! [X2] : ~(! [X3] : ~(r1_tarski(X2,X3) & r2_hidden(X3,X1)) & r2_hidden(X2,X0)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).
% 0.20/0.54  % SZS output end Proof for theBenchmark
% 0.20/0.54  % (13247)------------------------------
% 0.20/0.54  % (13247)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (13247)Termination reason: Refutation
% 0.20/0.54  
% 0.20/0.54  % (13247)Memory used [KB]: 6268
% 0.20/0.54  % (13247)Time elapsed: 0.131 s
% 0.20/0.54  % (13247)------------------------------
% 0.20/0.54  % (13247)------------------------------
% 0.20/0.54  % (13239)Success in time 0.187 s
%------------------------------------------------------------------------------
