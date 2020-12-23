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
% DateTime   : Thu Dec  3 12:37:49 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   17 (  43 expanded)
%              Number of leaves         :    4 (  14 expanded)
%              Depth                    :    6
%              Number of atoms          :   53 ( 167 expanded)
%              Number of equality atoms :   38 ( 123 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f16,f15,f12])).

fof(f12,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK0)
      | sK1 = X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,
    ( ! [X2] :
        ( sK1 = X2
        | ~ r2_hidden(X2,sK0) )
    & k1_xboole_0 != sK0
    & sK0 != k1_tarski(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f4,f6])).

fof(f6,plain,
    ( ? [X0,X1] :
        ( ! [X2] :
            ( X1 = X2
            | ~ r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 )
   => ( ! [X2] :
          ( sK1 = X2
          | ~ r2_hidden(X2,sK0) )
      & k1_xboole_0 != sK0
      & sK0 != k1_tarski(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f4,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ~ r2_hidden(X2,X0) )
      & k1_xboole_0 != X0
      & k1_tarski(X1) != X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ~ ( X1 != X2
                & r2_hidden(X2,X0) )
          & k1_xboole_0 != X0
          & k1_tarski(X1) != X0 ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).

fof(f15,plain,(
    r2_hidden(sK2(sK0,sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f11,f10,f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( sK2(X0,X1) != X1
        & r2_hidden(sK2(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f5,f8])).

fof(f8,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK2(X0,X1) != X1
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_zfmisc_1)).

% (19990)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
fof(f10,plain,(
    sK0 != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f11,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f7])).

fof(f16,plain,(
    sK1 != sK2(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f11,f10,f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( sK2(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:15:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (19998)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.47  % (19996)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.47  % (19998)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f19,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f16,f15,f12])).
% 0.22/0.47  fof(f12,plain,(
% 0.22/0.47    ( ! [X2] : (~r2_hidden(X2,sK0) | sK1 = X2) )),
% 0.22/0.47    inference(cnf_transformation,[],[f7])).
% 0.22/0.47  fof(f7,plain,(
% 0.22/0.47    ! [X2] : (sK1 = X2 | ~r2_hidden(X2,sK0)) & k1_xboole_0 != sK0 & sK0 != k1_tarski(sK1)),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f4,f6])).
% 0.22/0.47  fof(f6,plain,(
% 0.22/0.47    ? [X0,X1] : (! [X2] : (X1 = X2 | ~r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0) => (! [X2] : (sK1 = X2 | ~r2_hidden(X2,sK0)) & k1_xboole_0 != sK0 & sK0 != k1_tarski(sK1))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f4,plain,(
% 0.22/0.47    ? [X0,X1] : (! [X2] : (X1 = X2 | ~r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 0.22/0.47    inference(ennf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,negated_conjecture,(
% 0.22/0.47    ~! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 0.22/0.47    inference(negated_conjecture,[],[f2])).
% 0.22/0.47  fof(f2,conjecture,(
% 0.22/0.47    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    r2_hidden(sK2(sK0,sK1),sK0)),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f11,f10,f13])).
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 0.22/0.47    inference(cnf_transformation,[],[f9])).
% 0.22/0.47  fof(f9,plain,(
% 0.22/0.47    ! [X0,X1] : ((sK2(X0,X1) != X1 & r2_hidden(sK2(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f5,f8])).
% 0.22/0.47  fof(f8,plain,(
% 0.22/0.47    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK2(X0,X1) != X1 & r2_hidden(sK2(X0,X1),X0)))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f5,plain,(
% 0.22/0.47    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 0.22/0.47    inference(ennf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_zfmisc_1)).
% 0.22/0.47  % (19990)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.47  fof(f10,plain,(
% 0.22/0.47    sK0 != k1_tarski(sK1)),
% 0.22/0.47    inference(cnf_transformation,[],[f7])).
% 0.22/0.47  fof(f11,plain,(
% 0.22/0.47    k1_xboole_0 != sK0),
% 0.22/0.47    inference(cnf_transformation,[],[f7])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    sK1 != sK2(sK0,sK1)),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f11,f10,f14])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    ( ! [X0,X1] : (sK2(X0,X1) != X1 | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 0.22/0.47    inference(cnf_transformation,[],[f9])).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (19998)------------------------------
% 0.22/0.47  % (19998)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (19998)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (19998)Memory used [KB]: 6012
% 0.22/0.47  % (19998)Time elapsed: 0.005 s
% 0.22/0.47  % (19998)------------------------------
% 0.22/0.47  % (19998)------------------------------
% 0.22/0.47  % (19982)Success in time 0.11 s
%------------------------------------------------------------------------------
