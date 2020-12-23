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
% DateTime   : Thu Dec  3 12:58:15 EST 2020

% Result     : Theorem 1.17s
% Output     : Refutation 1.17s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 162 expanded)
%              Number of leaves         :   16 (  51 expanded)
%              Depth                    :   12
%              Number of atoms          :  100 ( 250 expanded)
%              Number of equality atoms :   44 ( 139 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f77,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f69,f64,f70,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f70,plain,(
    r1_tarski(sK2,k2_mcart_1(sK0)) ),
    inference(forward_demodulation,[],[f67,f53])).

fof(f53,plain,(
    ! [X0] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f28,f51])).

fof(f51,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f29,f49])).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f32,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f38,f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f41,f46])).

fof(f46,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f42,f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f43,f44])).

fof(f44,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f43,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f41,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f38,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f32,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f29,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f28,plain,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

fof(f67,plain,(
    r1_tarski(k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k2_mcart_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f60,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

fof(f60,plain,(
    r2_hidden(k2_mcart_1(sK0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(unit_resulting_resolution,[],[f52,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f52,plain,(
    r2_hidden(sK0,k2_zfmisc_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) ),
    inference(definition_unfolding,[],[f26,f51])).

fof(f26,plain,(
    r2_hidden(sK0,k2_zfmisc_1(sK1,k1_tarski(sK2))) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ( sK2 != k2_mcart_1(sK0)
      | ~ r2_hidden(k1_mcart_1(sK0),sK1) )
    & r2_hidden(sK0,k2_zfmisc_1(sK1,k1_tarski(sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f22])).

fof(f22,plain,
    ( ? [X0,X1,X2] :
        ( ( k2_mcart_1(X0) != X2
          | ~ r2_hidden(k1_mcart_1(X0),X1) )
        & r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))) )
   => ( ( sK2 != k2_mcart_1(sK0)
        | ~ r2_hidden(k1_mcart_1(sK0),sK1) )
      & r2_hidden(sK0,k2_zfmisc_1(sK1,k1_tarski(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ( k2_mcart_1(X0) != X2
        | ~ r2_hidden(k1_mcart_1(X0),X1) )
      & r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2)))
       => ( k2_mcart_1(X0) = X2
          & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2)))
     => ( k2_mcart_1(X0) = X2
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_mcart_1)).

fof(f64,plain,(
    sK2 != k2_mcart_1(sK0) ),
    inference(unit_resulting_resolution,[],[f61,f27])).

fof(f27,plain,
    ( ~ r2_hidden(k1_mcart_1(sK0),sK1)
    | sK2 != k2_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f61,plain,(
    r2_hidden(k1_mcart_1(sK0),sK1) ),
    inference(unit_resulting_resolution,[],[f52,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f69,plain,(
    r1_tarski(k2_mcart_1(sK0),sK2) ),
    inference(forward_demodulation,[],[f68,f54])).

fof(f54,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f30,f50])).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f31,f49])).

fof(f31,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f30,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f68,plain,(
    r1_tarski(k2_mcart_1(sK0),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) ),
    inference(unit_resulting_resolution,[],[f60,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:39:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.50  % (2282)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.17/0.51  % (2280)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.17/0.51  % (2291)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.17/0.51  % (2286)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.17/0.51  % (2286)Refutation found. Thanks to Tanya!
% 1.17/0.51  % SZS status Theorem for theBenchmark
% 1.17/0.51  % SZS output start Proof for theBenchmark
% 1.17/0.51  fof(f77,plain,(
% 1.17/0.51    $false),
% 1.17/0.51    inference(unit_resulting_resolution,[],[f69,f64,f70,f37])).
% 1.17/0.51  fof(f37,plain,(
% 1.17/0.51    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.17/0.51    inference(cnf_transformation,[],[f25])).
% 1.17/0.51  fof(f25,plain,(
% 1.17/0.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.17/0.51    inference(flattening,[],[f24])).
% 1.17/0.51  fof(f24,plain,(
% 1.17/0.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.17/0.51    inference(nnf_transformation,[],[f2])).
% 1.17/0.51  fof(f2,axiom,(
% 1.17/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.17/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.17/0.51  fof(f70,plain,(
% 1.17/0.51    r1_tarski(sK2,k2_mcart_1(sK0))),
% 1.17/0.51    inference(forward_demodulation,[],[f67,f53])).
% 1.17/0.51  fof(f53,plain,(
% 1.17/0.51    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 1.17/0.51    inference(definition_unfolding,[],[f28,f51])).
% 1.17/0.51  fof(f51,plain,(
% 1.17/0.51    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.17/0.51    inference(definition_unfolding,[],[f29,f49])).
% 1.17/0.51  fof(f49,plain,(
% 1.17/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.17/0.51    inference(definition_unfolding,[],[f32,f48])).
% 1.17/0.51  fof(f48,plain,(
% 1.17/0.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.17/0.51    inference(definition_unfolding,[],[f38,f47])).
% 1.17/0.51  fof(f47,plain,(
% 1.17/0.51    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.17/0.51    inference(definition_unfolding,[],[f41,f46])).
% 1.17/0.51  fof(f46,plain,(
% 1.17/0.51    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.17/0.51    inference(definition_unfolding,[],[f42,f45])).
% 1.17/0.51  fof(f45,plain,(
% 1.17/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.17/0.51    inference(definition_unfolding,[],[f43,f44])).
% 1.17/0.51  fof(f44,plain,(
% 1.17/0.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.17/0.51    inference(cnf_transformation,[],[f9])).
% 1.17/0.51  fof(f9,axiom,(
% 1.17/0.51    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.17/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 1.17/0.51  fof(f43,plain,(
% 1.17/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.17/0.51    inference(cnf_transformation,[],[f8])).
% 1.17/0.51  fof(f8,axiom,(
% 1.17/0.51    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.17/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.17/0.51  fof(f42,plain,(
% 1.17/0.51    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.17/0.51    inference(cnf_transformation,[],[f7])).
% 1.17/0.51  fof(f7,axiom,(
% 1.17/0.51    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.17/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.17/0.51  fof(f41,plain,(
% 1.17/0.51    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.17/0.51    inference(cnf_transformation,[],[f6])).
% 1.17/0.51  fof(f6,axiom,(
% 1.17/0.51    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.17/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.17/0.51  fof(f38,plain,(
% 1.17/0.51    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.17/0.51    inference(cnf_transformation,[],[f5])).
% 1.17/0.51  fof(f5,axiom,(
% 1.17/0.51    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.17/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.17/0.51  fof(f32,plain,(
% 1.17/0.51    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.17/0.51    inference(cnf_transformation,[],[f4])).
% 1.17/0.51  fof(f4,axiom,(
% 1.17/0.51    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.17/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.17/0.51  fof(f29,plain,(
% 1.17/0.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.17/0.51    inference(cnf_transformation,[],[f3])).
% 1.17/0.51  fof(f3,axiom,(
% 1.17/0.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.17/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.17/0.51  fof(f28,plain,(
% 1.17/0.51    ( ! [X0] : (k1_setfam_1(k1_tarski(X0)) = X0) )),
% 1.17/0.51    inference(cnf_transformation,[],[f12])).
% 1.17/0.51  fof(f12,axiom,(
% 1.17/0.51    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 1.17/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).
% 1.17/0.51  fof(f67,plain,(
% 1.17/0.51    r1_tarski(k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k2_mcart_1(sK0))),
% 1.17/0.51    inference(unit_resulting_resolution,[],[f60,f34])).
% 1.17/0.51  fof(f34,plain,(
% 1.17/0.51    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1)) )),
% 1.17/0.51    inference(cnf_transformation,[],[f20])).
% 1.17/0.51  fof(f20,plain,(
% 1.17/0.51    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1))),
% 1.17/0.51    inference(ennf_transformation,[],[f13])).
% 1.17/0.51  fof(f13,axiom,(
% 1.17/0.51    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 1.17/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).
% 1.17/0.51  fof(f60,plain,(
% 1.17/0.51    r2_hidden(k2_mcart_1(sK0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),
% 1.17/0.51    inference(unit_resulting_resolution,[],[f52,f40])).
% 1.17/0.51  fof(f40,plain,(
% 1.17/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 1.17/0.51    inference(cnf_transformation,[],[f21])).
% 1.17/0.51  fof(f21,plain,(
% 1.17/0.51    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.17/0.51    inference(ennf_transformation,[],[f14])).
% 1.17/0.51  fof(f14,axiom,(
% 1.17/0.51    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 1.17/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 1.17/0.51  fof(f52,plain,(
% 1.17/0.51    r2_hidden(sK0,k2_zfmisc_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))),
% 1.17/0.51    inference(definition_unfolding,[],[f26,f51])).
% 1.17/0.51  fof(f26,plain,(
% 1.17/0.51    r2_hidden(sK0,k2_zfmisc_1(sK1,k1_tarski(sK2)))),
% 1.17/0.51    inference(cnf_transformation,[],[f23])).
% 1.17/0.51  fof(f23,plain,(
% 1.17/0.51    (sK2 != k2_mcart_1(sK0) | ~r2_hidden(k1_mcart_1(sK0),sK1)) & r2_hidden(sK0,k2_zfmisc_1(sK1,k1_tarski(sK2)))),
% 1.17/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f22])).
% 1.17/0.51  fof(f22,plain,(
% 1.17/0.51    ? [X0,X1,X2] : ((k2_mcart_1(X0) != X2 | ~r2_hidden(k1_mcart_1(X0),X1)) & r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2)))) => ((sK2 != k2_mcart_1(sK0) | ~r2_hidden(k1_mcart_1(sK0),sK1)) & r2_hidden(sK0,k2_zfmisc_1(sK1,k1_tarski(sK2))))),
% 1.17/0.51    introduced(choice_axiom,[])).
% 1.17/0.51  fof(f18,plain,(
% 1.17/0.51    ? [X0,X1,X2] : ((k2_mcart_1(X0) != X2 | ~r2_hidden(k1_mcart_1(X0),X1)) & r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))))),
% 1.17/0.51    inference(ennf_transformation,[],[f16])).
% 1.17/0.51  fof(f16,negated_conjecture,(
% 1.17/0.51    ~! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))) => (k2_mcart_1(X0) = X2 & r2_hidden(k1_mcart_1(X0),X1)))),
% 1.17/0.51    inference(negated_conjecture,[],[f15])).
% 1.17/0.51  fof(f15,conjecture,(
% 1.17/0.51    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))) => (k2_mcart_1(X0) = X2 & r2_hidden(k1_mcart_1(X0),X1)))),
% 1.17/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_mcart_1)).
% 1.17/0.51  fof(f64,plain,(
% 1.17/0.51    sK2 != k2_mcart_1(sK0)),
% 1.17/0.51    inference(unit_resulting_resolution,[],[f61,f27])).
% 1.17/0.51  fof(f27,plain,(
% 1.17/0.51    ~r2_hidden(k1_mcart_1(sK0),sK1) | sK2 != k2_mcart_1(sK0)),
% 1.17/0.51    inference(cnf_transformation,[],[f23])).
% 1.17/0.51  fof(f61,plain,(
% 1.17/0.51    r2_hidden(k1_mcart_1(sK0),sK1)),
% 1.17/0.51    inference(unit_resulting_resolution,[],[f52,f39])).
% 1.17/0.51  fof(f39,plain,(
% 1.17/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 1.17/0.51    inference(cnf_transformation,[],[f21])).
% 1.17/0.51  fof(f69,plain,(
% 1.17/0.51    r1_tarski(k2_mcart_1(sK0),sK2)),
% 1.17/0.51    inference(forward_demodulation,[],[f68,f54])).
% 1.17/0.51  fof(f54,plain,(
% 1.17/0.51    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 1.17/0.51    inference(definition_unfolding,[],[f30,f50])).
% 1.17/0.51  fof(f50,plain,(
% 1.17/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.17/0.51    inference(definition_unfolding,[],[f31,f49])).
% 1.17/0.51  fof(f31,plain,(
% 1.17/0.51    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 1.17/0.51    inference(cnf_transformation,[],[f11])).
% 1.17/0.51  fof(f11,axiom,(
% 1.17/0.51    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 1.17/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.17/0.51  fof(f30,plain,(
% 1.17/0.51    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 1.17/0.51    inference(cnf_transformation,[],[f17])).
% 1.17/0.51  fof(f17,plain,(
% 1.17/0.51    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 1.17/0.51    inference(rectify,[],[f1])).
% 1.17/0.51  fof(f1,axiom,(
% 1.17/0.51    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 1.17/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 1.17/0.51  fof(f68,plain,(
% 1.17/0.51    r1_tarski(k2_mcart_1(sK0),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))),
% 1.17/0.51    inference(unit_resulting_resolution,[],[f60,f33])).
% 1.17/0.51  fof(f33,plain,(
% 1.17/0.51    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 1.17/0.51    inference(cnf_transformation,[],[f19])).
% 1.17/0.51  fof(f19,plain,(
% 1.17/0.51    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 1.17/0.51    inference(ennf_transformation,[],[f10])).
% 1.17/0.51  fof(f10,axiom,(
% 1.17/0.51    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 1.17/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 1.17/0.51  % SZS output end Proof for theBenchmark
% 1.17/0.51  % (2286)------------------------------
% 1.17/0.51  % (2286)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.17/0.51  % (2286)Termination reason: Refutation
% 1.17/0.51  
% 1.17/0.51  % (2286)Memory used [KB]: 1663
% 1.17/0.51  % (2286)Time elapsed: 0.106 s
% 1.17/0.51  % (2286)------------------------------
% 1.17/0.51  % (2286)------------------------------
% 1.17/0.51  % (2296)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.17/0.52  % (2276)Success in time 0.156 s
%------------------------------------------------------------------------------
