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
% DateTime   : Thu Dec  3 12:58:23 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   36 (  69 expanded)
%              Number of leaves         :    6 (  19 expanded)
%              Depth                    :   13
%              Number of atoms          :  102 ( 223 expanded)
%              Number of equality atoms :   41 (  97 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f43,plain,(
    $false ),
    inference(subsumption_resolution,[],[f42,f30])).

fof(f30,plain,(
    sK2 != k2_mcart_1(sK0) ),
    inference(subsumption_resolution,[],[f16,f29])).

fof(f29,plain,(
    r2_hidden(k1_mcart_1(sK0),sK1) ),
    inference(resolution,[],[f21,f15])).

fof(f15,plain,(
    r2_hidden(sK0,k2_zfmisc_1(sK1,k2_tarski(sK2,sK3))) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ( ( sK3 != k2_mcart_1(sK0)
        & sK2 != k2_mcart_1(sK0) )
      | ~ r2_hidden(k1_mcart_1(sK0),sK1) )
    & r2_hidden(sK0,k2_zfmisc_1(sK1,k2_tarski(sK2,sK3))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ( k2_mcart_1(X0) != X3
            & k2_mcart_1(X0) != X2 )
          | ~ r2_hidden(k1_mcart_1(X0),X1) )
        & r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))) )
   => ( ( ( sK3 != k2_mcart_1(sK0)
          & sK2 != k2_mcart_1(sK0) )
        | ~ r2_hidden(k1_mcart_1(sK0),sK1) )
      & r2_hidden(sK0,k2_zfmisc_1(sK1,k2_tarski(sK2,sK3))) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ( k2_mcart_1(X0) != X3
          & k2_mcart_1(X0) != X2 )
        | ~ r2_hidden(k1_mcart_1(X0),X1) )
      & r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3)))
       => ( ( k2_mcart_1(X0) = X3
            | k2_mcart_1(X0) = X2 )
          & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3)))
     => ( ( k2_mcart_1(X0) = X3
          | k2_mcart_1(X0) = X2 )
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_mcart_1)).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f16,plain,
    ( ~ r2_hidden(k1_mcart_1(sK0),sK1)
    | sK2 != k2_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f42,plain,(
    sK2 = k2_mcart_1(sK0) ),
    inference(subsumption_resolution,[],[f41,f31])).

fof(f31,plain,(
    sK3 != k2_mcart_1(sK0) ),
    inference(subsumption_resolution,[],[f17,f29])).

fof(f17,plain,
    ( ~ r2_hidden(k1_mcart_1(sK0),sK1)
    | sK3 != k2_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f41,plain,
    ( sK3 = k2_mcart_1(sK0)
    | sK2 = k2_mcart_1(sK0) ),
    inference(resolution,[],[f40,f32])).

fof(f32,plain,(
    r2_hidden(k2_mcart_1(sK0),k2_tarski(sK2,sK3)) ),
    inference(resolution,[],[f22,f15])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_tarski(X1,X2))
      | X0 = X2
      | X0 = X1 ) ),
    inference(condensation,[],[f39])).

fof(f39,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X3
      | X0 = X2
      | ~ r2_hidden(X1,X4)
      | ~ r2_hidden(X0,k2_tarski(X2,X3)) ) ),
    inference(forward_demodulation,[],[f38,f19])).

fof(f19,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X2
      | k1_mcart_1(k4_tarski(X0,X1)) = X3
      | ~ r2_hidden(X1,X4)
      | ~ r2_hidden(X0,k2_tarski(X2,X3)) ) ),
    inference(forward_demodulation,[],[f37,f19])).

fof(f37,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_mcart_1(k4_tarski(X0,X1)) = X2
      | k1_mcart_1(k4_tarski(X0,X1)) = X3
      | ~ r2_hidden(X1,X4)
      | ~ r2_hidden(X0,k2_tarski(X2,X3)) ) ),
    inference(resolution,[],[f24,f28])).

fof(f28,plain,(
    ! [X4,X2,X3,X1] :
      ( r2_hidden(k4_tarski(X3,X4),k2_zfmisc_1(X1,X2))
      | ~ r2_hidden(X4,X2)
      | ~ r2_hidden(X3,X1) ) ),
    inference(forward_demodulation,[],[f27,f19])).

fof(f27,plain,(
    ! [X4,X2,X3,X1] :
      ( ~ r2_hidden(X4,X2)
      | r2_hidden(k4_tarski(X3,X4),k2_zfmisc_1(X1,X2))
      | ~ r2_hidden(k1_mcart_1(k4_tarski(X3,X4)),X1) ) ),
    inference(forward_demodulation,[],[f26,f20])).

fof(f20,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X4,X2,X3,X1] :
      ( r2_hidden(k4_tarski(X3,X4),k2_zfmisc_1(X1,X2))
      | ~ r2_hidden(k2_mcart_1(k4_tarski(X3,X4)),X2)
      | ~ r2_hidden(k1_mcart_1(k4_tarski(X3,X4)),X1) ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | k4_tarski(X3,X4) != X0
      | ~ r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | ! [X3,X4] : k4_tarski(X3,X4) != X0
      | ~ r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | ! [X3,X4] : k4_tarski(X3,X4) != X0
      | ~ r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
     => ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
        | ! [X3,X4] : k4_tarski(X3,X4) != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_mcart_1)).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3))
      | k1_mcart_1(X0) = X1
      | k1_mcart_1(X0) = X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k2_mcart_1(X0),X3)
        & ( k1_mcart_1(X0) = X2
          | k1_mcart_1(X0) = X1 ) )
      | ~ r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3))
     => ( r2_hidden(k2_mcart_1(X0),X3)
        & ( k1_mcart_1(X0) = X2
          | k1_mcart_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n005.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 09:28:02 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.21/0.49  % (22472)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.49  % (22478)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.49  % (22478)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(subsumption_resolution,[],[f42,f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    sK2 != k2_mcart_1(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f16,f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    r2_hidden(k1_mcart_1(sK0),sK1)),
% 0.21/0.49    inference(resolution,[],[f21,f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    r2_hidden(sK0,k2_zfmisc_1(sK1,k2_tarski(sK2,sK3)))),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ((sK3 != k2_mcart_1(sK0) & sK2 != k2_mcart_1(sK0)) | ~r2_hidden(k1_mcart_1(sK0),sK1)) & r2_hidden(sK0,k2_zfmisc_1(sK1,k2_tarski(sK2,sK3)))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3] : (((k2_mcart_1(X0) != X3 & k2_mcart_1(X0) != X2) | ~r2_hidden(k1_mcart_1(X0),X1)) & r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3)))) => (((sK3 != k2_mcart_1(sK0) & sK2 != k2_mcart_1(sK0)) | ~r2_hidden(k1_mcart_1(sK0),sK1)) & r2_hidden(sK0,k2_zfmisc_1(sK1,k2_tarski(sK2,sK3))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3] : (((k2_mcart_1(X0) != X3 & k2_mcart_1(X0) != X2) | ~r2_hidden(k1_mcart_1(X0),X1)) & r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))) => ((k2_mcart_1(X0) = X3 | k2_mcart_1(X0) = X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.21/0.49    inference(negated_conjecture,[],[f6])).
% 0.21/0.49  fof(f6,conjecture,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))) => ((k2_mcart_1(X0) = X3 | k2_mcart_1(X0) = X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_mcart_1)).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ~r2_hidden(k1_mcart_1(sK0),sK1) | sK2 != k2_mcart_1(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    sK2 = k2_mcart_1(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f41,f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    sK3 != k2_mcart_1(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f17,f29])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ~r2_hidden(k1_mcart_1(sK0),sK1) | sK3 != k2_mcart_1(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    sK3 = k2_mcart_1(sK0) | sK2 = k2_mcart_1(sK0)),
% 0.21/0.49    inference(resolution,[],[f40,f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    r2_hidden(k2_mcart_1(sK0),k2_tarski(sK2,sK3))),
% 0.21/0.49    inference(resolution,[],[f22,f15])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_tarski(X1,X2)) | X0 = X2 | X0 = X1) )),
% 0.21/0.49    inference(condensation,[],[f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X3,X1] : (X0 = X3 | X0 = X2 | ~r2_hidden(X1,X4) | ~r2_hidden(X0,k2_tarski(X2,X3))) )),
% 0.21/0.49    inference(forward_demodulation,[],[f38,f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X3,X1] : (X0 = X2 | k1_mcart_1(k4_tarski(X0,X1)) = X3 | ~r2_hidden(X1,X4) | ~r2_hidden(X0,k2_tarski(X2,X3))) )),
% 0.21/0.49    inference(forward_demodulation,[],[f37,f19])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X3,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X2 | k1_mcart_1(k4_tarski(X0,X1)) = X3 | ~r2_hidden(X1,X4) | ~r2_hidden(X0,k2_tarski(X2,X3))) )),
% 0.21/0.49    inference(resolution,[],[f24,f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ( ! [X4,X2,X3,X1] : (r2_hidden(k4_tarski(X3,X4),k2_zfmisc_1(X1,X2)) | ~r2_hidden(X4,X2) | ~r2_hidden(X3,X1)) )),
% 0.21/0.49    inference(forward_demodulation,[],[f27,f19])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ( ! [X4,X2,X3,X1] : (~r2_hidden(X4,X2) | r2_hidden(k4_tarski(X3,X4),k2_zfmisc_1(X1,X2)) | ~r2_hidden(k1_mcart_1(k4_tarski(X3,X4)),X1)) )),
% 0.21/0.49    inference(forward_demodulation,[],[f26,f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f5])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ( ! [X4,X2,X3,X1] : (r2_hidden(k4_tarski(X3,X4),k2_zfmisc_1(X1,X2)) | ~r2_hidden(k2_mcart_1(k4_tarski(X3,X4)),X2) | ~r2_hidden(k1_mcart_1(k4_tarski(X3,X4)),X1)) )),
% 0.21/0.49    inference(equality_resolution,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) | k4_tarski(X3,X4) != X0 | ~r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(k1_mcart_1(X0),X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) | ! [X3,X4] : k4_tarski(X3,X4) != X0 | ~r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(k1_mcart_1(X0),X1))),
% 0.21/0.49    inference(flattening,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((r2_hidden(X0,k2_zfmisc_1(X1,X2)) | ! [X3,X4] : k4_tarski(X3,X4) != X0) | (~r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(k1_mcart_1(X0),X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) => (r2_hidden(X0,k2_zfmisc_1(X1,X2)) | ! [X3,X4] : k4_tarski(X3,X4) != X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_mcart_1)).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)) | k1_mcart_1(X0) = X1 | k1_mcart_1(X0) = X2) )),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : ((r2_hidden(k2_mcart_1(X0),X3) & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)) | ~r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)) => (r2_hidden(k2_mcart_1(X0),X3) & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_mcart_1)).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (22478)------------------------------
% 0.21/0.49  % (22478)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (22478)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (22478)Memory used [KB]: 6140
% 0.21/0.49  % (22478)Time elapsed: 0.034 s
% 0.21/0.49  % (22478)------------------------------
% 0.21/0.49  % (22478)------------------------------
% 0.21/0.49  % (22480)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.50  % (22470)Success in time 0.137 s
%------------------------------------------------------------------------------
