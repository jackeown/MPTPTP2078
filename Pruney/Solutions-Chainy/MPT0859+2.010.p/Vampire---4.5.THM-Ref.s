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
% DateTime   : Thu Dec  3 12:58:21 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   28 (  60 expanded)
%              Number of leaves         :    5 (  15 expanded)
%              Depth                    :    9
%              Number of atoms          :   68 ( 145 expanded)
%              Number of equality atoms :   41 (  75 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f53,plain,(
    $false ),
    inference(subsumption_resolution,[],[f52,f44])).

fof(f44,plain,(
    sK2 != k1_mcart_1(sK0) ),
    inference(resolution,[],[f43,f11])).

fof(f11,plain,
    ( ~ r2_hidden(k2_mcart_1(sK0),sK3)
    | sK2 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r2_hidden(k2_mcart_1(X0),X3)
        | ( k1_mcart_1(X0) != X2
          & k1_mcart_1(X0) != X1 ) )
      & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3))
       => ( r2_hidden(k2_mcart_1(X0),X3)
          & ( k1_mcart_1(X0) = X2
            | k1_mcart_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3))
     => ( r2_hidden(k2_mcart_1(X0),X3)
        & ( k1_mcart_1(X0) = X2
          | k1_mcart_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_mcart_1)).

fof(f43,plain,(
    r2_hidden(k2_mcart_1(sK0),sK3) ),
    inference(resolution,[],[f16,f28])).

fof(f28,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK2),sK3)) ),
    inference(definition_unfolding,[],[f12,f27])).

fof(f27,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f13,f14])).

fof(f14,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f13,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f12,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),sK3)) ),
    inference(cnf_transformation,[],[f7])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f52,plain,(
    sK2 = k1_mcart_1(sK0) ),
    inference(subsumption_resolution,[],[f51,f45])).

fof(f45,plain,(
    sK1 != k1_mcart_1(sK0) ),
    inference(resolution,[],[f43,f10])).

fof(f10,plain,
    ( ~ r2_hidden(k2_mcart_1(sK0),sK3)
    | sK1 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f51,plain,
    ( sK1 = k1_mcart_1(sK0)
    | sK2 = k1_mcart_1(sK0) ),
    inference(duplicate_literal_removal,[],[f50])).

fof(f50,plain,
    ( sK1 = k1_mcart_1(sK0)
    | sK1 = k1_mcart_1(sK0)
    | sK2 = k1_mcart_1(sK0)
    | sK1 = k1_mcart_1(sK0) ),
    inference(resolution,[],[f37,f42])).

fof(f42,plain,(
    r2_hidden(k1_mcart_1(sK0),k2_enumset1(sK1,sK1,sK1,sK2)) ),
    inference(resolution,[],[f15,f28])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f37,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(X5,k2_enumset1(X0,X1,X2,X3))
      | X1 = X5
      | X2 = X5
      | X3 = X5
      | X0 = X5 ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( X0 = X5
      | X1 = X5
      | X2 = X5
      | X3 = X5
      | ~ r2_hidden(X5,X4)
      | k2_enumset1(X0,X1,X2,X3) != X4 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ( X3 = X5
            | X2 = X5
            | X1 = X5
            | X0 = X5 ) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X3 != X5
              & X2 != X5
              & X1 != X5
              & X0 != X5 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:29:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.55  % (13227)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.55  % (13227)Refutation found. Thanks to Tanya!
% 0.20/0.55  % SZS status Theorem for theBenchmark
% 0.20/0.55  % SZS output start Proof for theBenchmark
% 0.20/0.55  fof(f53,plain,(
% 0.20/0.55    $false),
% 0.20/0.55    inference(subsumption_resolution,[],[f52,f44])).
% 0.20/0.55  fof(f44,plain,(
% 0.20/0.55    sK2 != k1_mcart_1(sK0)),
% 0.20/0.55    inference(resolution,[],[f43,f11])).
% 0.20/0.55  fof(f11,plain,(
% 0.20/0.55    ~r2_hidden(k2_mcart_1(sK0),sK3) | sK2 != k1_mcart_1(sK0)),
% 0.20/0.55    inference(cnf_transformation,[],[f7])).
% 0.20/0.55  fof(f7,plain,(
% 0.20/0.55    ? [X0,X1,X2,X3] : ((~r2_hidden(k2_mcart_1(X0),X3) | (k1_mcart_1(X0) != X2 & k1_mcart_1(X0) != X1)) & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)))),
% 0.20/0.55    inference(ennf_transformation,[],[f6])).
% 0.20/0.55  fof(f6,negated_conjecture,(
% 0.20/0.55    ~! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)) => (r2_hidden(k2_mcart_1(X0),X3) & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)))),
% 0.20/0.55    inference(negated_conjecture,[],[f5])).
% 0.20/0.55  fof(f5,conjecture,(
% 0.20/0.55    ! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)) => (r2_hidden(k2_mcart_1(X0),X3) & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_mcart_1)).
% 0.20/0.55  fof(f43,plain,(
% 0.20/0.55    r2_hidden(k2_mcart_1(sK0),sK3)),
% 0.20/0.55    inference(resolution,[],[f16,f28])).
% 0.20/0.55  fof(f28,plain,(
% 0.20/0.55    r2_hidden(sK0,k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK2),sK3))),
% 0.20/0.55    inference(definition_unfolding,[],[f12,f27])).
% 0.20/0.55  fof(f27,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.20/0.55    inference(definition_unfolding,[],[f13,f14])).
% 0.20/0.55  fof(f14,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f2])).
% 0.20/0.55  fof(f2,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.55  fof(f13,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f1])).
% 0.20/0.55  fof(f1,axiom,(
% 0.20/0.55    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.55  fof(f12,plain,(
% 0.20/0.55    r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),sK3))),
% 0.20/0.55    inference(cnf_transformation,[],[f7])).
% 0.20/0.55  fof(f16,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f8])).
% 0.20/0.55  fof(f8,plain,(
% 0.20/0.55    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.20/0.55    inference(ennf_transformation,[],[f4])).
% 0.20/0.55  fof(f4,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.20/0.55  fof(f52,plain,(
% 0.20/0.55    sK2 = k1_mcart_1(sK0)),
% 0.20/0.55    inference(subsumption_resolution,[],[f51,f45])).
% 0.20/0.55  fof(f45,plain,(
% 0.20/0.55    sK1 != k1_mcart_1(sK0)),
% 0.20/0.55    inference(resolution,[],[f43,f10])).
% 0.20/0.55  fof(f10,plain,(
% 0.20/0.55    ~r2_hidden(k2_mcart_1(sK0),sK3) | sK1 != k1_mcart_1(sK0)),
% 0.20/0.55    inference(cnf_transformation,[],[f7])).
% 0.20/0.55  fof(f51,plain,(
% 0.20/0.55    sK1 = k1_mcart_1(sK0) | sK2 = k1_mcart_1(sK0)),
% 0.20/0.55    inference(duplicate_literal_removal,[],[f50])).
% 0.20/0.55  fof(f50,plain,(
% 0.20/0.55    sK1 = k1_mcart_1(sK0) | sK1 = k1_mcart_1(sK0) | sK2 = k1_mcart_1(sK0) | sK1 = k1_mcart_1(sK0)),
% 0.20/0.55    inference(resolution,[],[f37,f42])).
% 0.20/0.55  fof(f42,plain,(
% 0.20/0.55    r2_hidden(k1_mcart_1(sK0),k2_enumset1(sK1,sK1,sK1,sK2))),
% 0.20/0.55    inference(resolution,[],[f15,f28])).
% 0.20/0.55  fof(f15,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f8])).
% 0.20/0.55  fof(f37,plain,(
% 0.20/0.55    ( ! [X2,X0,X5,X3,X1] : (~r2_hidden(X5,k2_enumset1(X0,X1,X2,X3)) | X1 = X5 | X2 = X5 | X3 = X5 | X0 = X5) )),
% 0.20/0.55    inference(equality_resolution,[],[f22])).
% 0.20/0.55  fof(f22,plain,(
% 0.20/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (X0 = X5 | X1 = X5 | X2 = X5 | X3 = X5 | ~r2_hidden(X5,X4) | k2_enumset1(X0,X1,X2,X3) != X4) )),
% 0.20/0.55    inference(cnf_transformation,[],[f9])).
% 0.20/0.55  fof(f9,plain,(
% 0.20/0.55    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> ! [X5] : (r2_hidden(X5,X4) <=> (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5)))),
% 0.20/0.55    inference(ennf_transformation,[],[f3])).
% 0.20/0.55  fof(f3,axiom,(
% 0.20/0.55    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> ! [X5] : (r2_hidden(X5,X4) <=> ~(X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_enumset1)).
% 0.20/0.55  % SZS output end Proof for theBenchmark
% 0.20/0.55  % (13227)------------------------------
% 0.20/0.55  % (13227)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (13227)Termination reason: Refutation
% 0.20/0.55  
% 0.20/0.55  % (13227)Memory used [KB]: 6140
% 0.20/0.55  % (13227)Time elapsed: 0.119 s
% 0.20/0.55  % (13227)------------------------------
% 0.20/0.55  % (13227)------------------------------
% 0.20/0.56  % (13220)Success in time 0.19 s
%------------------------------------------------------------------------------
