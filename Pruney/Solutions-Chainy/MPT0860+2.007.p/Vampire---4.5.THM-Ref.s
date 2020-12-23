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
% DateTime   : Thu Dec  3 12:58:22 EST 2020

% Result     : Theorem 1.32s
% Output     : Refutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :   37 (  86 expanded)
%              Number of leaves         :    7 (  23 expanded)
%              Depth                    :   10
%              Number of atoms          :   90 ( 194 expanded)
%              Number of equality atoms :   40 (  93 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f131,plain,(
    $false ),
    inference(resolution,[],[f127,f32])).

fof(f32,plain,(
    r2_hidden(sK0,k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK3))) ),
    inference(definition_unfolding,[],[f14,f31])).

fof(f31,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f15,f18])).

fof(f18,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f15,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f14,plain,(
    r2_hidden(sK0,k2_zfmisc_1(sK1,k2_tarski(sK2,sK3))) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ( k2_mcart_1(X0) != X3
          & k2_mcart_1(X0) != X2 )
        | ~ r2_hidden(k1_mcart_1(X0),X1) )
      & r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3)))
       => ( ( k2_mcart_1(X0) = X3
            | k2_mcart_1(X0) = X2 )
          & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3)))
     => ( ( k2_mcart_1(X0) = X3
          | k2_mcart_1(X0) = X2 )
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_mcart_1)).

fof(f127,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,X1) ),
    inference(subsumption_resolution,[],[f126,f41])).

fof(f41,plain,(
    sK3 != k2_mcart_1(sK0) ),
    inference(resolution,[],[f40,f13])).

fof(f13,plain,
    ( ~ r2_hidden(k1_mcart_1(sK0),sK1)
    | sK3 != k2_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f40,plain,(
    r2_hidden(k1_mcart_1(sK0),sK1) ),
    inference(resolution,[],[f19,f32])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f126,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | sK3 = k2_mcart_1(sK0) ) ),
    inference(subsumption_resolution,[],[f118,f42])).

fof(f42,plain,(
    sK2 != k2_mcart_1(sK0) ),
    inference(resolution,[],[f40,f12])).

fof(f12,plain,
    ( ~ r2_hidden(k1_mcart_1(sK0),sK1)
    | sK2 != k2_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f118,plain,(
    ! [X0,X1] :
      ( sK2 = k2_mcart_1(sK0)
      | ~ r2_hidden(X0,X1)
      | sK3 = k2_mcart_1(sK0) ) ),
    inference(resolution,[],[f117,f43])).

fof(f43,plain,(
    r2_hidden(k2_mcart_1(sK0),k2_enumset1(sK2,sK2,sK2,sK3)) ),
    inference(resolution,[],[f20,f32])).

% (32302)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f117,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k2_enumset1(X2,X2,X2,X3))
      | X0 = X2
      | ~ r2_hidden(X1,X4)
      | X0 = X3 ) ),
    inference(forward_demodulation,[],[f116,f16])).

fof(f16,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f116,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X2
      | k1_mcart_1(k4_tarski(X0,X1)) = X3
      | ~ r2_hidden(X1,X4)
      | ~ r2_hidden(X0,k2_enumset1(X2,X2,X2,X3)) ) ),
    inference(forward_demodulation,[],[f109,f16])).

fof(f109,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_mcart_1(k4_tarski(X0,X1)) = X2
      | k1_mcart_1(k4_tarski(X0,X1)) = X3
      | ~ r2_hidden(X1,X4)
      | ~ r2_hidden(X0,k2_enumset1(X2,X2,X2,X3)) ) ),
    inference(resolution,[],[f34,f36])).

fof(f36,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | r2_hidden(k4_tarski(X4,X5),X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f28])).

% (32298)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
fof(f28,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | k4_tarski(X4,X5) != X3
      | r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k2_enumset1(X1,X1,X1,X2),X3))
      | k1_mcart_1(X0) = X1
      | k1_mcart_1(X0) = X2 ) ),
    inference(definition_unfolding,[],[f29,f31])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3))
      | k1_mcart_1(X0) = X1
      | k1_mcart_1(X0) = X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k2_mcart_1(X0),X3)
        & ( k1_mcart_1(X0) = X2
          | k1_mcart_1(X0) = X1 ) )
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3))
     => ( r2_hidden(k2_mcart_1(X0),X3)
        & ( k1_mcart_1(X0) = X2
          | k1_mcart_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:20:18 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.52  % (32284)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (32286)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (32290)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.32/0.53  % (32292)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.32/0.53  % (32284)Refutation found. Thanks to Tanya!
% 1.32/0.53  % SZS status Theorem for theBenchmark
% 1.32/0.54  % (32300)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.32/0.54  % SZS output start Proof for theBenchmark
% 1.32/0.54  fof(f131,plain,(
% 1.32/0.54    $false),
% 1.32/0.54    inference(resolution,[],[f127,f32])).
% 1.32/0.54  fof(f32,plain,(
% 1.32/0.54    r2_hidden(sK0,k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK3)))),
% 1.32/0.54    inference(definition_unfolding,[],[f14,f31])).
% 1.32/0.54  fof(f31,plain,(
% 1.32/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.32/0.54    inference(definition_unfolding,[],[f15,f18])).
% 1.32/0.54  fof(f18,plain,(
% 1.32/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f2])).
% 1.32/0.54  fof(f2,axiom,(
% 1.32/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.32/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.32/0.54  fof(f15,plain,(
% 1.32/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f1])).
% 1.32/0.54  fof(f1,axiom,(
% 1.32/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.32/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.32/0.54  fof(f14,plain,(
% 1.32/0.54    r2_hidden(sK0,k2_zfmisc_1(sK1,k2_tarski(sK2,sK3)))),
% 1.32/0.54    inference(cnf_transformation,[],[f9])).
% 1.32/0.54  fof(f9,plain,(
% 1.32/0.54    ? [X0,X1,X2,X3] : (((k2_mcart_1(X0) != X3 & k2_mcart_1(X0) != X2) | ~r2_hidden(k1_mcart_1(X0),X1)) & r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))))),
% 1.32/0.54    inference(ennf_transformation,[],[f8])).
% 1.32/0.54  fof(f8,negated_conjecture,(
% 1.32/0.54    ~! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))) => ((k2_mcart_1(X0) = X3 | k2_mcart_1(X0) = X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 1.32/0.54    inference(negated_conjecture,[],[f7])).
% 1.32/0.54  fof(f7,conjecture,(
% 1.32/0.54    ! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))) => ((k2_mcart_1(X0) = X3 | k2_mcart_1(X0) = X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 1.32/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_mcart_1)).
% 1.32/0.54  fof(f127,plain,(
% 1.32/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1)) )),
% 1.32/0.54    inference(subsumption_resolution,[],[f126,f41])).
% 1.32/0.54  fof(f41,plain,(
% 1.32/0.54    sK3 != k2_mcart_1(sK0)),
% 1.32/0.54    inference(resolution,[],[f40,f13])).
% 1.32/0.54  fof(f13,plain,(
% 1.32/0.54    ~r2_hidden(k1_mcart_1(sK0),sK1) | sK3 != k2_mcart_1(sK0)),
% 1.32/0.54    inference(cnf_transformation,[],[f9])).
% 1.32/0.54  fof(f40,plain,(
% 1.32/0.54    r2_hidden(k1_mcart_1(sK0),sK1)),
% 1.32/0.54    inference(resolution,[],[f19,f32])).
% 1.32/0.54  fof(f19,plain,(
% 1.32/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f10])).
% 1.32/0.54  fof(f10,plain,(
% 1.32/0.54    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.32/0.54    inference(ennf_transformation,[],[f4])).
% 1.32/0.54  fof(f4,axiom,(
% 1.32/0.54    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 1.32/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 1.32/0.54  fof(f126,plain,(
% 1.32/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | sK3 = k2_mcart_1(sK0)) )),
% 1.32/0.54    inference(subsumption_resolution,[],[f118,f42])).
% 1.32/0.54  fof(f42,plain,(
% 1.32/0.54    sK2 != k2_mcart_1(sK0)),
% 1.32/0.54    inference(resolution,[],[f40,f12])).
% 1.32/0.54  fof(f12,plain,(
% 1.32/0.54    ~r2_hidden(k1_mcart_1(sK0),sK1) | sK2 != k2_mcart_1(sK0)),
% 1.32/0.54    inference(cnf_transformation,[],[f9])).
% 1.32/0.54  fof(f118,plain,(
% 1.32/0.54    ( ! [X0,X1] : (sK2 = k2_mcart_1(sK0) | ~r2_hidden(X0,X1) | sK3 = k2_mcart_1(sK0)) )),
% 1.32/0.54    inference(resolution,[],[f117,f43])).
% 1.32/0.54  fof(f43,plain,(
% 1.32/0.54    r2_hidden(k2_mcart_1(sK0),k2_enumset1(sK2,sK2,sK2,sK3))),
% 1.32/0.54    inference(resolution,[],[f20,f32])).
% 1.32/0.54  % (32302)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.32/0.54  fof(f20,plain,(
% 1.32/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f10])).
% 1.32/0.54  fof(f117,plain,(
% 1.32/0.54    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X0,k2_enumset1(X2,X2,X2,X3)) | X0 = X2 | ~r2_hidden(X1,X4) | X0 = X3) )),
% 1.32/0.54    inference(forward_demodulation,[],[f116,f16])).
% 1.32/0.54  fof(f16,plain,(
% 1.32/0.54    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 1.32/0.54    inference(cnf_transformation,[],[f6])).
% 1.32/0.54  fof(f6,axiom,(
% 1.32/0.54    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 1.32/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).
% 1.32/0.54  fof(f116,plain,(
% 1.32/0.54    ( ! [X4,X2,X0,X3,X1] : (X0 = X2 | k1_mcart_1(k4_tarski(X0,X1)) = X3 | ~r2_hidden(X1,X4) | ~r2_hidden(X0,k2_enumset1(X2,X2,X2,X3))) )),
% 1.32/0.54    inference(forward_demodulation,[],[f109,f16])).
% 1.32/0.54  fof(f109,plain,(
% 1.32/0.54    ( ! [X4,X2,X0,X3,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X2 | k1_mcart_1(k4_tarski(X0,X1)) = X3 | ~r2_hidden(X1,X4) | ~r2_hidden(X0,k2_enumset1(X2,X2,X2,X3))) )),
% 1.32/0.54    inference(resolution,[],[f34,f36])).
% 1.32/0.54  fof(f36,plain,(
% 1.32/0.54    ( ! [X4,X0,X5,X1] : (r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1)) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) )),
% 1.32/0.54    inference(equality_resolution,[],[f35])).
% 1.32/0.54  fof(f35,plain,(
% 1.32/0.54    ( ! [X4,X2,X0,X5,X1] : (~r2_hidden(X4,X0) | ~r2_hidden(X5,X1) | r2_hidden(k4_tarski(X4,X5),X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.32/0.54    inference(equality_resolution,[],[f28])).
% 1.32/0.54  % (32298)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.32/0.54  fof(f28,plain,(
% 1.32/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (~r2_hidden(X4,X0) | ~r2_hidden(X5,X1) | k4_tarski(X4,X5) != X3 | r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.32/0.54    inference(cnf_transformation,[],[f3])).
% 1.32/0.54  fof(f3,axiom,(
% 1.32/0.54    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 1.32/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 1.32/0.54  fof(f34,plain,(
% 1.32/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,k2_zfmisc_1(k2_enumset1(X1,X1,X1,X2),X3)) | k1_mcart_1(X0) = X1 | k1_mcart_1(X0) = X2) )),
% 1.32/0.54    inference(definition_unfolding,[],[f29,f31])).
% 1.32/0.54  fof(f29,plain,(
% 1.32/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)) | k1_mcart_1(X0) = X1 | k1_mcart_1(X0) = X2) )),
% 1.32/0.54    inference(cnf_transformation,[],[f11])).
% 1.32/0.54  fof(f11,plain,(
% 1.32/0.54    ! [X0,X1,X2,X3] : ((r2_hidden(k2_mcart_1(X0),X3) & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)) | ~r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)))),
% 1.32/0.54    inference(ennf_transformation,[],[f5])).
% 1.32/0.54  fof(f5,axiom,(
% 1.32/0.54    ! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)) => (r2_hidden(k2_mcart_1(X0),X3) & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)))),
% 1.32/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_mcart_1)).
% 1.32/0.54  % SZS output end Proof for theBenchmark
% 1.32/0.54  % (32284)------------------------------
% 1.32/0.54  % (32284)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.54  % (32284)Termination reason: Refutation
% 1.32/0.54  
% 1.32/0.54  % (32284)Memory used [KB]: 6396
% 1.32/0.54  % (32284)Time elapsed: 0.117 s
% 1.32/0.54  % (32284)------------------------------
% 1.32/0.54  % (32284)------------------------------
% 1.32/0.54  % (32277)Success in time 0.185 s
%------------------------------------------------------------------------------
