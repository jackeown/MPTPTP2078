%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:17 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   30 (  59 expanded)
%              Number of leaves         :    7 (  17 expanded)
%              Depth                    :   11
%              Number of atoms          :   71 ( 157 expanded)
%              Number of equality atoms :   28 (  59 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f58,plain,(
    $false ),
    inference(subsumption_resolution,[],[f57,f33])).

fof(f33,plain,(
    r2_hidden(k1_mcart_1(sK0),sK1) ),
    inference(resolution,[],[f19,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f19,plain,(
    r2_hidden(sK0,k2_zfmisc_1(sK1,k1_tarski(sK2))) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ( sK2 != k2_mcart_1(sK0)
      | ~ r2_hidden(k1_mcart_1(sK0),sK1) )
    & r2_hidden(sK0,k2_zfmisc_1(sK1,k1_tarski(sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( ( k2_mcart_1(X0) != X2
          | ~ r2_hidden(k1_mcart_1(X0),X1) )
        & r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))) )
   => ( ( sK2 != k2_mcart_1(sK0)
        | ~ r2_hidden(k1_mcart_1(sK0),sK1) )
      & r2_hidden(sK0,k2_zfmisc_1(sK1,k1_tarski(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ( k2_mcart_1(X0) != X2
        | ~ r2_hidden(k1_mcart_1(X0),X1) )
      & r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2)))
       => ( k2_mcart_1(X0) = X2
          & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2)))
     => ( k2_mcart_1(X0) = X2
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_mcart_1)).

fof(f57,plain,(
    ~ r2_hidden(k1_mcart_1(sK0),sK1) ),
    inference(trivial_inequality_removal,[],[f56])).

fof(f56,plain,
    ( sK2 != sK2
    | ~ r2_hidden(k1_mcart_1(sK0),sK1) ),
    inference(backward_demodulation,[],[f20,f50])).

fof(f50,plain,(
    sK2 = k2_mcart_1(sK0) ),
    inference(resolution,[],[f44,f19])).

fof(f44,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(sK0,k2_zfmisc_1(X2,k1_tarski(X3)))
      | k2_mcart_1(sK0) = X3 ) ),
    inference(forward_demodulation,[],[f39,f37])).

fof(f37,plain,(
    k2_mcart_1(sK0) = sK4(sK0) ),
    inference(superposition,[],[f26,f35])).

fof(f35,plain,(
    sK0 = k4_tarski(sK3(sK0),sK4(sK0)) ),
    inference(resolution,[],[f19,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | k4_tarski(sK3(X0),sK4(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k4_tarski(sK3(X0),sK4(X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f11,f17])).

fof(f17,plain,(
    ! [X0] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
     => k4_tarski(sK3(X0),sK4(X0)) = X0 ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( ! [X3,X4] : k4_tarski(X3,X4) != X0
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).

fof(f26,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f39,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(sK0,k2_zfmisc_1(X2,k1_tarski(X3)))
      | sK4(sK0) = X3 ) ),
    inference(superposition,[],[f22,f35])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
        | X1 != X3
        | ~ r2_hidden(X0,X2) )
      & ( ( X1 = X3
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
        | X1 != X3
        | ~ r2_hidden(X0,X2) )
      & ( ( X1 = X3
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
    <=> ( X1 = X3
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_zfmisc_1)).

fof(f20,plain,
    ( sK2 != k2_mcart_1(sK0)
    | ~ r2_hidden(k1_mcart_1(sK0),sK1) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:21:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.18/0.51  % (13318)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.18/0.52  % (13326)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.18/0.52  % (13326)Refutation found. Thanks to Tanya!
% 0.18/0.52  % SZS status Theorem for theBenchmark
% 0.18/0.52  % SZS output start Proof for theBenchmark
% 0.18/0.52  fof(f58,plain,(
% 0.18/0.52    $false),
% 0.18/0.52    inference(subsumption_resolution,[],[f57,f33])).
% 0.18/0.52  fof(f33,plain,(
% 0.18/0.52    r2_hidden(k1_mcart_1(sK0),sK1)),
% 0.18/0.52    inference(resolution,[],[f19,f29])).
% 0.18/0.52  fof(f29,plain,(
% 0.18/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 0.18/0.52    inference(cnf_transformation,[],[f12])).
% 0.18/0.52  fof(f12,plain,(
% 0.18/0.52    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.18/0.52    inference(ennf_transformation,[],[f6])).
% 0.18/0.52  fof(f6,axiom,(
% 0.18/0.52    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.18/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.18/0.52  fof(f19,plain,(
% 0.18/0.52    r2_hidden(sK0,k2_zfmisc_1(sK1,k1_tarski(sK2)))),
% 0.18/0.52    inference(cnf_transformation,[],[f14])).
% 0.18/0.52  fof(f14,plain,(
% 0.18/0.52    (sK2 != k2_mcart_1(sK0) | ~r2_hidden(k1_mcart_1(sK0),sK1)) & r2_hidden(sK0,k2_zfmisc_1(sK1,k1_tarski(sK2)))),
% 0.18/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f13])).
% 0.18/0.52  fof(f13,plain,(
% 0.18/0.52    ? [X0,X1,X2] : ((k2_mcart_1(X0) != X2 | ~r2_hidden(k1_mcart_1(X0),X1)) & r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2)))) => ((sK2 != k2_mcart_1(sK0) | ~r2_hidden(k1_mcart_1(sK0),sK1)) & r2_hidden(sK0,k2_zfmisc_1(sK1,k1_tarski(sK2))))),
% 0.18/0.52    introduced(choice_axiom,[])).
% 0.18/0.52  fof(f10,plain,(
% 0.18/0.52    ? [X0,X1,X2] : ((k2_mcart_1(X0) != X2 | ~r2_hidden(k1_mcart_1(X0),X1)) & r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))))),
% 0.18/0.52    inference(ennf_transformation,[],[f9])).
% 0.18/0.52  fof(f9,negated_conjecture,(
% 0.18/0.52    ~! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))) => (k2_mcart_1(X0) = X2 & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.18/0.52    inference(negated_conjecture,[],[f8])).
% 0.18/0.52  fof(f8,conjecture,(
% 0.18/0.52    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))) => (k2_mcart_1(X0) = X2 & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.18/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_mcart_1)).
% 0.18/0.52  fof(f57,plain,(
% 0.18/0.52    ~r2_hidden(k1_mcart_1(sK0),sK1)),
% 0.18/0.52    inference(trivial_inequality_removal,[],[f56])).
% 0.18/0.52  fof(f56,plain,(
% 0.18/0.52    sK2 != sK2 | ~r2_hidden(k1_mcart_1(sK0),sK1)),
% 0.18/0.52    inference(backward_demodulation,[],[f20,f50])).
% 0.18/0.52  fof(f50,plain,(
% 0.18/0.52    sK2 = k2_mcart_1(sK0)),
% 0.18/0.52    inference(resolution,[],[f44,f19])).
% 0.18/0.52  fof(f44,plain,(
% 0.18/0.52    ( ! [X2,X3] : (~r2_hidden(sK0,k2_zfmisc_1(X2,k1_tarski(X3))) | k2_mcart_1(sK0) = X3) )),
% 0.18/0.52    inference(forward_demodulation,[],[f39,f37])).
% 0.18/0.52  fof(f37,plain,(
% 0.18/0.52    k2_mcart_1(sK0) = sK4(sK0)),
% 0.18/0.52    inference(superposition,[],[f26,f35])).
% 0.18/0.52  fof(f35,plain,(
% 0.18/0.52    sK0 = k4_tarski(sK3(sK0),sK4(sK0))),
% 0.18/0.52    inference(resolution,[],[f19,f24])).
% 0.18/0.52  fof(f24,plain,(
% 0.18/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | k4_tarski(sK3(X0),sK4(X0)) = X0) )),
% 0.18/0.52    inference(cnf_transformation,[],[f18])).
% 0.18/0.52  fof(f18,plain,(
% 0.18/0.52    ! [X0,X1,X2] : (k4_tarski(sK3(X0),sK4(X0)) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.18/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f11,f17])).
% 0.18/0.52  fof(f17,plain,(
% 0.18/0.52    ! [X0] : (? [X3,X4] : k4_tarski(X3,X4) = X0 => k4_tarski(sK3(X0),sK4(X0)) = X0)),
% 0.18/0.52    introduced(choice_axiom,[])).
% 0.18/0.52  fof(f11,plain,(
% 0.18/0.52    ! [X0,X1,X2] : (? [X3,X4] : k4_tarski(X3,X4) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.18/0.52    inference(ennf_transformation,[],[f4])).
% 0.18/0.52  fof(f4,axiom,(
% 0.18/0.52    ! [X0,X1,X2] : ~(! [X3,X4] : k4_tarski(X3,X4) != X0 & r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.18/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).
% 0.18/0.52  fof(f26,plain,(
% 0.18/0.52    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.18/0.52    inference(cnf_transformation,[],[f7])).
% 0.18/0.52  fof(f7,axiom,(
% 0.18/0.52    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.18/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.18/0.52  fof(f39,plain,(
% 0.18/0.52    ( ! [X2,X3] : (~r2_hidden(sK0,k2_zfmisc_1(X2,k1_tarski(X3))) | sK4(sK0) = X3) )),
% 0.18/0.52    inference(superposition,[],[f22,f35])).
% 0.18/0.52  fof(f22,plain,(
% 0.18/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | X1 = X3) )),
% 0.18/0.52    inference(cnf_transformation,[],[f16])).
% 0.18/0.52  fof(f16,plain,(
% 0.18/0.52    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | X1 != X3 | ~r2_hidden(X0,X2)) & ((X1 = X3 & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))))),
% 0.18/0.52    inference(flattening,[],[f15])).
% 0.18/0.52  fof(f15,plain,(
% 0.18/0.52    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | (X1 != X3 | ~r2_hidden(X0,X2))) & ((X1 = X3 & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))))),
% 0.18/0.52    inference(nnf_transformation,[],[f5])).
% 0.18/0.52  fof(f5,axiom,(
% 0.18/0.52    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) <=> (X1 = X3 & r2_hidden(X0,X2)))),
% 0.18/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_zfmisc_1)).
% 0.18/0.52  fof(f20,plain,(
% 0.18/0.52    sK2 != k2_mcart_1(sK0) | ~r2_hidden(k1_mcart_1(sK0),sK1)),
% 0.18/0.52    inference(cnf_transformation,[],[f14])).
% 0.18/0.52  % SZS output end Proof for theBenchmark
% 0.18/0.52  % (13326)------------------------------
% 0.18/0.52  % (13326)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.52  % (13326)Termination reason: Refutation
% 0.18/0.52  
% 0.18/0.52  % (13326)Memory used [KB]: 1663
% 0.18/0.52  % (13326)Time elapsed: 0.115 s
% 0.18/0.52  % (13326)------------------------------
% 0.18/0.52  % (13326)------------------------------
% 0.18/0.53  % (13311)Success in time 0.187 s
%------------------------------------------------------------------------------
