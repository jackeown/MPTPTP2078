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
% DateTime   : Thu Dec  3 12:58:21 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   30 (  98 expanded)
%              Number of leaves         :    5 (  24 expanded)
%              Depth                    :   10
%              Number of atoms          :   61 ( 243 expanded)
%              Number of equality atoms :   28 ( 114 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f110,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f69,f11,f37])).

fof(f37,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(sK0,k2_zfmisc_1(X2,X3))
      | r2_hidden(k1_mcart_1(sK0),X2) ) ),
    inference(backward_demodulation,[],[f31,f33])).

fof(f33,plain,(
    k1_mcart_1(sK0) = sK5(sK0) ),
    inference(superposition,[],[f12,f29])).

fof(f29,plain,(
    sK0 = k4_tarski(sK5(sK0),sK6(sK0)) ),
    inference(unit_resulting_resolution,[],[f11,f20])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | k4_tarski(sK5(X0),sK6(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ~ ( ! [X3,X4] : k4_tarski(X3,X4) != X0
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).

fof(f12,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f31,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(sK0,k2_zfmisc_1(X2,X3))
      | r2_hidden(sK5(sK0),X2) ) ),
    inference(superposition,[],[f21,f29])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(f11,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),sK3)) ),
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

fof(f69,plain,(
    ~ r2_hidden(k1_mcart_1(sK0),k2_tarski(sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f51,f52,f28])).

fof(f28,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_tarski(X0,X1))
      | X1 = X3
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f17])).

fof(f17,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f52,plain,(
    sK1 != k1_mcart_1(sK0) ),
    inference(unit_resulting_resolution,[],[f50,f9])).

fof(f9,plain,
    ( ~ r2_hidden(k2_mcart_1(sK0),sK3)
    | sK1 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f50,plain,(
    r2_hidden(k2_mcart_1(sK0),sK3) ),
    inference(unit_resulting_resolution,[],[f11,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK0,k2_zfmisc_1(X0,X1))
      | r2_hidden(k2_mcart_1(sK0),X1) ) ),
    inference(backward_demodulation,[],[f30,f32])).

fof(f32,plain,(
    k2_mcart_1(sK0) = sK6(sK0) ),
    inference(superposition,[],[f13,f29])).

fof(f13,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f4])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK0,k2_zfmisc_1(X0,X1))
      | r2_hidden(sK6(sK0),X1) ) ),
    inference(superposition,[],[f22,f29])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f51,plain,(
    sK2 != k1_mcart_1(sK0) ),
    inference(unit_resulting_resolution,[],[f50,f10])).

fof(f10,plain,
    ( ~ r2_hidden(k2_mcart_1(sK0),sK3)
    | sK2 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n023.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 15:01:20 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.23/0.48  % (18687)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.23/0.49  % (18679)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.23/0.49  % (18679)Refutation found. Thanks to Tanya!
% 0.23/0.49  % SZS status Theorem for theBenchmark
% 0.23/0.49  % SZS output start Proof for theBenchmark
% 0.23/0.49  fof(f110,plain,(
% 0.23/0.49    $false),
% 0.23/0.49    inference(unit_resulting_resolution,[],[f69,f11,f37])).
% 0.23/0.49  fof(f37,plain,(
% 0.23/0.49    ( ! [X2,X3] : (~r2_hidden(sK0,k2_zfmisc_1(X2,X3)) | r2_hidden(k1_mcart_1(sK0),X2)) )),
% 0.23/0.49    inference(backward_demodulation,[],[f31,f33])).
% 0.23/0.49  fof(f33,plain,(
% 0.23/0.49    k1_mcart_1(sK0) = sK5(sK0)),
% 0.23/0.49    inference(superposition,[],[f12,f29])).
% 0.23/0.49  fof(f29,plain,(
% 0.23/0.49    sK0 = k4_tarski(sK5(sK0),sK6(sK0))),
% 0.23/0.49    inference(unit_resulting_resolution,[],[f11,f20])).
% 0.23/0.49  fof(f20,plain,(
% 0.23/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | k4_tarski(sK5(X0),sK6(X0)) = X0) )),
% 0.23/0.49    inference(cnf_transformation,[],[f8])).
% 0.23/0.49  fof(f8,plain,(
% 0.23/0.49    ! [X0,X1,X2] : (? [X3,X4] : k4_tarski(X3,X4) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.23/0.49    inference(ennf_transformation,[],[f2])).
% 0.23/0.49  fof(f2,axiom,(
% 0.23/0.49    ! [X0,X1,X2] : ~(! [X3,X4] : k4_tarski(X3,X4) != X0 & r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).
% 0.23/0.49  fof(f12,plain,(
% 0.23/0.49    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.23/0.49    inference(cnf_transformation,[],[f4])).
% 0.23/0.49  fof(f4,axiom,(
% 0.23/0.49    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.23/0.49  fof(f31,plain,(
% 0.23/0.49    ( ! [X2,X3] : (~r2_hidden(sK0,k2_zfmisc_1(X2,X3)) | r2_hidden(sK5(sK0),X2)) )),
% 0.23/0.49    inference(superposition,[],[f21,f29])).
% 0.23/0.49  fof(f21,plain,(
% 0.23/0.49    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f3])).
% 0.23/0.49  fof(f3,axiom,(
% 0.23/0.49    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).
% 0.23/0.49  fof(f11,plain,(
% 0.23/0.49    r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),sK3))),
% 0.23/0.49    inference(cnf_transformation,[],[f7])).
% 0.23/0.49  fof(f7,plain,(
% 0.23/0.49    ? [X0,X1,X2,X3] : ((~r2_hidden(k2_mcart_1(X0),X3) | (k1_mcart_1(X0) != X2 & k1_mcart_1(X0) != X1)) & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)))),
% 0.23/0.49    inference(ennf_transformation,[],[f6])).
% 0.23/0.49  fof(f6,negated_conjecture,(
% 0.23/0.49    ~! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)) => (r2_hidden(k2_mcart_1(X0),X3) & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)))),
% 0.23/0.49    inference(negated_conjecture,[],[f5])).
% 0.23/0.49  fof(f5,conjecture,(
% 0.23/0.49    ! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)) => (r2_hidden(k2_mcart_1(X0),X3) & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_mcart_1)).
% 0.23/0.49  fof(f69,plain,(
% 0.23/0.49    ~r2_hidden(k1_mcart_1(sK0),k2_tarski(sK1,sK2))),
% 0.23/0.49    inference(unit_resulting_resolution,[],[f51,f52,f28])).
% 0.23/0.49  fof(f28,plain,(
% 0.23/0.49    ( ! [X0,X3,X1] : (~r2_hidden(X3,k2_tarski(X0,X1)) | X1 = X3 | X0 = X3) )),
% 0.23/0.49    inference(equality_resolution,[],[f17])).
% 0.23/0.49  fof(f17,plain,(
% 0.23/0.49    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 0.23/0.49    inference(cnf_transformation,[],[f1])).
% 0.23/0.49  fof(f1,axiom,(
% 0.23/0.49    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 0.23/0.49  fof(f52,plain,(
% 0.23/0.49    sK1 != k1_mcart_1(sK0)),
% 0.23/0.49    inference(unit_resulting_resolution,[],[f50,f9])).
% 0.23/0.49  fof(f9,plain,(
% 0.23/0.49    ~r2_hidden(k2_mcart_1(sK0),sK3) | sK1 != k1_mcart_1(sK0)),
% 0.23/0.49    inference(cnf_transformation,[],[f7])).
% 0.23/0.49  fof(f50,plain,(
% 0.23/0.49    r2_hidden(k2_mcart_1(sK0),sK3)),
% 0.23/0.49    inference(unit_resulting_resolution,[],[f11,f34])).
% 0.23/0.49  fof(f34,plain,(
% 0.23/0.49    ( ! [X0,X1] : (~r2_hidden(sK0,k2_zfmisc_1(X0,X1)) | r2_hidden(k2_mcart_1(sK0),X1)) )),
% 0.23/0.49    inference(backward_demodulation,[],[f30,f32])).
% 0.23/0.49  fof(f32,plain,(
% 0.23/0.49    k2_mcart_1(sK0) = sK6(sK0)),
% 0.23/0.49    inference(superposition,[],[f13,f29])).
% 0.23/0.49  fof(f13,plain,(
% 0.23/0.49    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.23/0.49    inference(cnf_transformation,[],[f4])).
% 0.23/0.49  fof(f30,plain,(
% 0.23/0.49    ( ! [X0,X1] : (~r2_hidden(sK0,k2_zfmisc_1(X0,X1)) | r2_hidden(sK6(sK0),X1)) )),
% 0.23/0.49    inference(superposition,[],[f22,f29])).
% 0.23/0.49  fof(f22,plain,(
% 0.23/0.49    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f3])).
% 0.23/0.49  fof(f51,plain,(
% 0.23/0.49    sK2 != k1_mcart_1(sK0)),
% 0.23/0.49    inference(unit_resulting_resolution,[],[f50,f10])).
% 0.23/0.49  fof(f10,plain,(
% 0.23/0.49    ~r2_hidden(k2_mcart_1(sK0),sK3) | sK2 != k1_mcart_1(sK0)),
% 0.23/0.49    inference(cnf_transformation,[],[f7])).
% 0.23/0.49  % SZS output end Proof for theBenchmark
% 0.23/0.49  % (18679)------------------------------
% 0.23/0.49  % (18679)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.49  % (18679)Termination reason: Refutation
% 0.23/0.49  
% 0.23/0.49  % (18679)Memory used [KB]: 1791
% 0.23/0.49  % (18679)Time elapsed: 0.066 s
% 0.23/0.49  % (18679)------------------------------
% 0.23/0.49  % (18679)------------------------------
% 0.23/0.49  % (18671)Success in time 0.119 s
%------------------------------------------------------------------------------
