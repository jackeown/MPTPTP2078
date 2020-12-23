%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:19 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   39 ( 113 expanded)
%              Number of leaves         :    8 (  35 expanded)
%              Depth                    :   11
%              Number of atoms          :   83 ( 193 expanded)
%              Number of equality atoms :   45 ( 131 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f65,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f63])).

fof(f63,plain,(
    sK2 != sK2 ),
    inference(superposition,[],[f44,f62])).

fof(f62,plain,(
    sK2 = k2_mcart_1(sK0) ),
    inference(resolution,[],[f51,f33])).

fof(f33,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK2,sK2,sK2,sK2))) ),
    inference(definition_unfolding,[],[f19,f32,f32])).

fof(f32,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f28,f31])).

fof(f31,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f29,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f29,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f28,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f19,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),k1_tarski(sK2))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ( sK2 != k2_mcart_1(sK0)
      | sK1 != k1_mcart_1(sK0) )
    & r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),k1_tarski(sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ( k2_mcart_1(X0) != X2
          | k1_mcart_1(X0) != X1 )
        & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2))) )
   => ( ( sK2 != k2_mcart_1(sK0)
        | sK1 != k1_mcart_1(sK0) )
      & r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),k1_tarski(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ( k2_mcart_1(X0) != X2
        | k1_mcart_1(X0) != X1 )
      & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2)))
       => ( k2_mcart_1(X0) = X2
          & k1_mcart_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2)))
     => ( k2_mcart_1(X0) = X2
        & k1_mcart_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_mcart_1)).

fof(f51,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(X4,k2_zfmisc_1(k2_enumset1(X6,X6,X6,X6),k2_enumset1(X5,X5,X5,X5)))
      | k2_mcart_1(X4) = X5 ) ),
    inference(resolution,[],[f49,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X2)) ) ),
    inference(definition_unfolding,[],[f22,f32])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 )
      | ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).

fof(f49,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X3,k2_enumset1(X4,X4,X4,X4))
      | X3 = X4 ) ),
    inference(forward_demodulation,[],[f48,f23])).

fof(f23,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f48,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X3,k2_enumset1(X4,X4,X4,X4))
      | k1_mcart_1(k4_tarski(X3,X5)) = X4 ) ),
    inference(resolution,[],[f39,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X2))
      | k1_mcart_1(X0) = X1 ) ),
    inference(definition_unfolding,[],[f21,f32])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( k1_mcart_1(X0) = X1
      | ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f39,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(k4_tarski(X0,X3),k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3)))
      | ~ r2_hidden(X0,X2) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3)))
      | X1 != X3
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f27,f32])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
      | X1 != X3
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
        | X1 != X3
        | ~ r2_hidden(X0,X2) )
      & ( ( X1 = X3
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
        | X1 != X3
        | ~ r2_hidden(X0,X2) )
      & ( ( X1 = X3
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
    <=> ( X1 = X3
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_zfmisc_1)).

fof(f44,plain,(
    sK2 != k2_mcart_1(sK0) ),
    inference(trivial_inequality_removal,[],[f43])).

fof(f43,plain,
    ( sK1 != sK1
    | sK2 != k2_mcart_1(sK0) ),
    inference(backward_demodulation,[],[f20,f41])).

fof(f41,plain,(
    sK1 = k1_mcart_1(sK0) ),
    inference(resolution,[],[f35,f33])).

fof(f20,plain,
    ( sK2 != k2_mcart_1(sK0)
    | sK1 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:11:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.53  % (26390)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (26390)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f63])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    sK2 != sK2),
% 0.21/0.53    inference(superposition,[],[f44,f62])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    sK2 = k2_mcart_1(sK0)),
% 0.21/0.53    inference(resolution,[],[f51,f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    r2_hidden(sK0,k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK2,sK2,sK2,sK2)))),
% 0.21/0.53    inference(definition_unfolding,[],[f19,f32,f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f28,f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f29,f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),k1_tarski(sK2)))),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    (sK2 != k2_mcart_1(sK0) | sK1 != k1_mcart_1(sK0)) & r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),k1_tarski(sK2)))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ? [X0,X1,X2] : ((k2_mcart_1(X0) != X2 | k1_mcart_1(X0) != X1) & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2)))) => ((sK2 != k2_mcart_1(sK0) | sK1 != k1_mcart_1(sK0)) & r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),k1_tarski(sK2))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ? [X0,X1,X2] : ((k2_mcart_1(X0) != X2 | k1_mcart_1(X0) != X1) & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2))))),
% 0.21/0.53    inference(ennf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2))) => (k2_mcart_1(X0) = X2 & k1_mcart_1(X0) = X1))),
% 0.21/0.53    inference(negated_conjecture,[],[f11])).
% 0.21/0.53  fof(f11,conjecture,(
% 0.21/0.53    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2))) => (k2_mcart_1(X0) = X2 & k1_mcart_1(X0) = X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_mcart_1)).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X6,X4,X5] : (~r2_hidden(X4,k2_zfmisc_1(k2_enumset1(X6,X6,X6,X6),k2_enumset1(X5,X5,X5,X5))) | k2_mcart_1(X4) = X5) )),
% 0.21/0.53    inference(resolution,[],[f49,f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X2))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f22,f32])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1) | ~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) => (r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ( ! [X4,X3] : (~r2_hidden(X3,k2_enumset1(X4,X4,X4,X4)) | X3 = X4) )),
% 0.21/0.53    inference(forward_demodulation,[],[f48,f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ( ! [X4,X5,X3] : (~r2_hidden(X3,k2_enumset1(X4,X4,X4,X4)) | k1_mcart_1(k4_tarski(X3,X5)) = X4) )),
% 0.21/0.53    inference(resolution,[],[f39,f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X2)) | k1_mcart_1(X0) = X1) )),
% 0.21/0.53    inference(definition_unfolding,[],[f21,f32])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k1_mcart_1(X0) = X1 | ~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ( ! [X2,X0,X3] : (r2_hidden(k4_tarski(X0,X3),k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3))) | ~r2_hidden(X0,X2)) )),
% 0.21/0.53    inference(equality_resolution,[],[f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3))) | X1 != X3 | ~r2_hidden(X0,X2)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f27,f32])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | X1 != X3 | ~r2_hidden(X0,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | X1 != X3 | ~r2_hidden(X0,X2)) & ((X1 = X3 & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))))),
% 0.21/0.53    inference(flattening,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | (X1 != X3 | ~r2_hidden(X0,X2))) & ((X1 = X3 & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))))),
% 0.21/0.53    inference(nnf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) <=> (X1 = X3 & r2_hidden(X0,X2)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_zfmisc_1)).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    sK2 != k2_mcart_1(sK0)),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f43])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    sK1 != sK1 | sK2 != k2_mcart_1(sK0)),
% 0.21/0.53    inference(backward_demodulation,[],[f20,f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    sK1 = k1_mcart_1(sK0)),
% 0.21/0.53    inference(resolution,[],[f35,f33])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    sK2 != k2_mcart_1(sK0) | sK1 != k1_mcart_1(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (26390)------------------------------
% 0.21/0.53  % (26390)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (26390)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (26390)Memory used [KB]: 1663
% 0.21/0.53  % (26390)Time elapsed: 0.110 s
% 0.21/0.53  % (26390)------------------------------
% 0.21/0.53  % (26390)------------------------------
% 0.21/0.53  % (26384)Success in time 0.167 s
%------------------------------------------------------------------------------
