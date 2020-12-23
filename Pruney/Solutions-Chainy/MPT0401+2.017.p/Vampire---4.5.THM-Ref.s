%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:16 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   46 (  94 expanded)
%              Number of leaves         :   12 (  31 expanded)
%              Depth                    :   12
%              Number of atoms          :   83 ( 163 expanded)
%              Number of equality atoms :   14 (  50 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f113,plain,(
    $false ),
    inference(subsumption_resolution,[],[f112,f23])).

fof(f23,plain,(
    ~ r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ r1_tarski(sK2,sK0)
    & r2_hidden(sK2,sK1)
    & r1_setfam_1(sK1,k1_tarski(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f18,f17])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(X2,X0)
            & r2_hidden(X2,X1) )
        & r1_setfam_1(X1,k1_tarski(X0)) )
   => ( ? [X2] :
          ( ~ r1_tarski(X2,sK0)
          & r2_hidden(X2,sK1) )
      & r1_setfam_1(sK1,k1_tarski(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X2] :
        ( ~ r1_tarski(X2,sK0)
        & r2_hidden(X2,sK1) )
   => ( ~ r1_tarski(sK2,sK0)
      & r2_hidden(sK2,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,X0)
          & r2_hidden(X2,X1) )
      & r1_setfam_1(X1,k1_tarski(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_setfam_1(X1,k1_tarski(X0))
       => ! [X2] :
            ( r2_hidden(X2,X1)
           => r1_tarski(X2,X0) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( r1_setfam_1(X1,k1_tarski(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_setfam_1)).

fof(f112,plain,(
    r1_tarski(sK2,sK0) ),
    inference(forward_demodulation,[],[f111,f38])).

fof(f38,plain,(
    ! [X0] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f24,f36])).

fof(f36,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f25,f35])).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f26,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f31,f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f31,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f26,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f25,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f24,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

fof(f111,plain,(
    r1_tarski(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK2)),sK0) ),
    inference(forward_demodulation,[],[f110,f38])).

fof(f110,plain,(
    r1_tarski(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK2)),k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    inference(resolution,[],[f70,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_setfam_1(X0,X1)
      | r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_setfam_1)).

fof(f70,plain,(
    r1_setfam_1(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(resolution,[],[f69,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ r1_setfam_1(X0,sK1)
      | r1_setfam_1(X0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ) ),
    inference(resolution,[],[f32,f37])).

fof(f37,plain,(
    r1_setfam_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(definition_unfolding,[],[f21,f36])).

fof(f21,plain,(
    r1_setfam_1(sK1,k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_setfam_1(X1,X2)
      | r1_setfam_1(X0,X2)
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_setfam_1(X0,X2)
      | ~ r1_setfam_1(X1,X2)
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_setfam_1(X0,X2)
      | ~ r1_setfam_1(X1,X2)
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_setfam_1(X1,X2)
        & r1_setfam_1(X0,X1) )
     => r1_setfam_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_setfam_1)).

fof(f69,plain,(
    r1_setfam_1(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK1) ),
    inference(resolution,[],[f68,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_setfam_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_setfam_1)).

fof(f68,plain,(
    r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK1) ),
    inference(resolution,[],[f39,f22])).

fof(f22,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f30,f36])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:05:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.41  % (12558)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.41  % (12558)Refutation found. Thanks to Tanya!
% 0.21/0.41  % SZS status Theorem for theBenchmark
% 0.21/0.41  % SZS output start Proof for theBenchmark
% 0.21/0.41  fof(f113,plain,(
% 0.21/0.41    $false),
% 0.21/0.41    inference(subsumption_resolution,[],[f112,f23])).
% 0.21/0.41  fof(f23,plain,(
% 0.21/0.41    ~r1_tarski(sK2,sK0)),
% 0.21/0.41    inference(cnf_transformation,[],[f19])).
% 0.21/0.41  fof(f19,plain,(
% 0.21/0.41    (~r1_tarski(sK2,sK0) & r2_hidden(sK2,sK1)) & r1_setfam_1(sK1,k1_tarski(sK0))),
% 0.21/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f18,f17])).
% 0.21/0.41  fof(f17,plain,(
% 0.21/0.41    ? [X0,X1] : (? [X2] : (~r1_tarski(X2,X0) & r2_hidden(X2,X1)) & r1_setfam_1(X1,k1_tarski(X0))) => (? [X2] : (~r1_tarski(X2,sK0) & r2_hidden(X2,sK1)) & r1_setfam_1(sK1,k1_tarski(sK0)))),
% 0.21/0.41    introduced(choice_axiom,[])).
% 0.21/0.41  fof(f18,plain,(
% 0.21/0.41    ? [X2] : (~r1_tarski(X2,sK0) & r2_hidden(X2,sK1)) => (~r1_tarski(sK2,sK0) & r2_hidden(sK2,sK1))),
% 0.21/0.41    introduced(choice_axiom,[])).
% 0.21/0.41  fof(f12,plain,(
% 0.21/0.41    ? [X0,X1] : (? [X2] : (~r1_tarski(X2,X0) & r2_hidden(X2,X1)) & r1_setfam_1(X1,k1_tarski(X0)))),
% 0.21/0.41    inference(ennf_transformation,[],[f11])).
% 0.21/0.41  fof(f11,negated_conjecture,(
% 0.21/0.41    ~! [X0,X1] : (r1_setfam_1(X1,k1_tarski(X0)) => ! [X2] : (r2_hidden(X2,X1) => r1_tarski(X2,X0)))),
% 0.21/0.41    inference(negated_conjecture,[],[f10])).
% 0.21/0.41  fof(f10,conjecture,(
% 0.21/0.41    ! [X0,X1] : (r1_setfam_1(X1,k1_tarski(X0)) => ! [X2] : (r2_hidden(X2,X1) => r1_tarski(X2,X0)))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_setfam_1)).
% 0.21/0.41  fof(f112,plain,(
% 0.21/0.41    r1_tarski(sK2,sK0)),
% 0.21/0.41    inference(forward_demodulation,[],[f111,f38])).
% 0.21/0.41  fof(f38,plain,(
% 0.21/0.41    ( ! [X0] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X0)) = X0) )),
% 0.21/0.41    inference(definition_unfolding,[],[f24,f36])).
% 0.21/0.41  fof(f36,plain,(
% 0.21/0.41    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 0.21/0.41    inference(definition_unfolding,[],[f25,f35])).
% 0.21/0.41  fof(f35,plain,(
% 0.21/0.41    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.21/0.41    inference(definition_unfolding,[],[f26,f34])).
% 0.21/0.41  fof(f34,plain,(
% 0.21/0.41    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.21/0.41    inference(definition_unfolding,[],[f31,f33])).
% 0.21/0.41  fof(f33,plain,(
% 0.21/0.41    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f4])).
% 0.21/0.41  fof(f4,axiom,(
% 0.21/0.41    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.41  fof(f31,plain,(
% 0.21/0.41    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f3])).
% 0.21/0.41  fof(f3,axiom,(
% 0.21/0.41    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.41  fof(f26,plain,(
% 0.21/0.41    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f2])).
% 0.21/0.41  fof(f2,axiom,(
% 0.21/0.41    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.41  fof(f25,plain,(
% 0.21/0.41    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f1])).
% 0.21/0.41  fof(f1,axiom,(
% 0.21/0.41    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.41  fof(f24,plain,(
% 0.21/0.41    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = X0) )),
% 0.21/0.41    inference(cnf_transformation,[],[f6])).
% 0.21/0.41  fof(f6,axiom,(
% 0.21/0.41    ! [X0] : k3_tarski(k1_tarski(X0)) = X0),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).
% 0.21/0.41  fof(f111,plain,(
% 0.21/0.41    r1_tarski(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK2)),sK0)),
% 0.21/0.41    inference(forward_demodulation,[],[f110,f38])).
% 0.21/0.41  fof(f110,plain,(
% 0.21/0.41    r1_tarski(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK2)),k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),
% 0.21/0.41    inference(resolution,[],[f70,f28])).
% 0.21/0.41  fof(f28,plain,(
% 0.21/0.41    ( ! [X0,X1] : (~r1_setfam_1(X0,X1) | r1_tarski(k3_tarski(X0),k3_tarski(X1))) )),
% 0.21/0.41    inference(cnf_transformation,[],[f14])).
% 0.21/0.41  fof(f14,plain,(
% 0.21/0.41    ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_setfam_1(X0,X1))),
% 0.21/0.41    inference(ennf_transformation,[],[f8])).
% 0.21/0.41  fof(f8,axiom,(
% 0.21/0.41    ! [X0,X1] : (r1_setfam_1(X0,X1) => r1_tarski(k3_tarski(X0),k3_tarski(X1)))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_setfam_1)).
% 0.21/0.41  fof(f70,plain,(
% 0.21/0.41    r1_setfam_1(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 0.21/0.41    inference(resolution,[],[f69,f57])).
% 0.21/0.41  fof(f57,plain,(
% 0.21/0.41    ( ! [X0] : (~r1_setfam_1(X0,sK1) | r1_setfam_1(X0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) )),
% 0.21/0.41    inference(resolution,[],[f32,f37])).
% 0.21/0.41  fof(f37,plain,(
% 0.21/0.41    r1_setfam_1(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 0.21/0.41    inference(definition_unfolding,[],[f21,f36])).
% 0.21/0.41  fof(f21,plain,(
% 0.21/0.41    r1_setfam_1(sK1,k1_tarski(sK0))),
% 0.21/0.41    inference(cnf_transformation,[],[f19])).
% 0.21/0.41  fof(f32,plain,(
% 0.21/0.41    ( ! [X2,X0,X1] : (~r1_setfam_1(X1,X2) | r1_setfam_1(X0,X2) | ~r1_setfam_1(X0,X1)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f16])).
% 0.21/0.41  fof(f16,plain,(
% 0.21/0.41    ! [X0,X1,X2] : (r1_setfam_1(X0,X2) | ~r1_setfam_1(X1,X2) | ~r1_setfam_1(X0,X1))),
% 0.21/0.41    inference(flattening,[],[f15])).
% 0.21/0.41  fof(f15,plain,(
% 0.21/0.41    ! [X0,X1,X2] : (r1_setfam_1(X0,X2) | (~r1_setfam_1(X1,X2) | ~r1_setfam_1(X0,X1)))),
% 0.21/0.41    inference(ennf_transformation,[],[f9])).
% 0.21/0.41  fof(f9,axiom,(
% 0.21/0.41    ! [X0,X1,X2] : ((r1_setfam_1(X1,X2) & r1_setfam_1(X0,X1)) => r1_setfam_1(X0,X2))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_setfam_1)).
% 0.21/0.41  fof(f69,plain,(
% 0.21/0.41    r1_setfam_1(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK1)),
% 0.21/0.41    inference(resolution,[],[f68,f27])).
% 0.21/0.41  fof(f27,plain,(
% 0.21/0.41    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r1_setfam_1(X0,X1)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f13])).
% 0.21/0.41  fof(f13,plain,(
% 0.21/0.41    ! [X0,X1] : (r1_setfam_1(X0,X1) | ~r1_tarski(X0,X1))),
% 0.21/0.41    inference(ennf_transformation,[],[f7])).
% 0.21/0.41  fof(f7,axiom,(
% 0.21/0.41    ! [X0,X1] : (r1_tarski(X0,X1) => r1_setfam_1(X0,X1))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_setfam_1)).
% 0.21/0.41  fof(f68,plain,(
% 0.21/0.41    r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK1)),
% 0.21/0.41    inference(resolution,[],[f39,f22])).
% 0.21/0.41  fof(f22,plain,(
% 0.21/0.41    r2_hidden(sK2,sK1)),
% 0.21/0.41    inference(cnf_transformation,[],[f19])).
% 0.21/0.41  fof(f39,plain,(
% 0.21/0.41    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k3_enumset1(X0,X0,X0,X0,X0),X1)) )),
% 0.21/0.41    inference(definition_unfolding,[],[f30,f36])).
% 0.21/0.41  fof(f30,plain,(
% 0.21/0.41    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f20])).
% 0.21/0.41  fof(f20,plain,(
% 0.21/0.41    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.21/0.41    inference(nnf_transformation,[],[f5])).
% 0.21/0.41  fof(f5,axiom,(
% 0.21/0.41    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.21/0.41  % SZS output end Proof for theBenchmark
% 0.21/0.41  % (12558)------------------------------
% 0.21/0.41  % (12558)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.41  % (12558)Termination reason: Refutation
% 0.21/0.41  
% 0.21/0.41  % (12558)Memory used [KB]: 1663
% 0.21/0.41  % (12558)Time elapsed: 0.007 s
% 0.21/0.41  % (12558)------------------------------
% 0.21/0.41  % (12558)------------------------------
% 0.21/0.41  % (12544)Success in time 0.06 s
%------------------------------------------------------------------------------
