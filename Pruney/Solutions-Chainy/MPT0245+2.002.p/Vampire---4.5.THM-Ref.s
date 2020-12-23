%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:45 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   14 (  26 expanded)
%              Number of leaves         :    3 (   7 expanded)
%              Depth                    :    6
%              Number of atoms          :   37 (  79 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f10,f11,f12,f13])).

fof(f13,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X0)
      | r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2)))
      | r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2)))
      | r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l2_zfmisc_1)).

fof(f12,plain,(
    ~ r1_tarski(sK0,k4_xboole_0(sK1,k1_tarski(sK2))) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,
    ( ~ r1_tarski(sK0,k4_xboole_0(sK1,k1_tarski(sK2)))
    & ~ r2_hidden(sK2,sK0)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f8])).

fof(f8,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2)))
        & ~ r2_hidden(X2,X0)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(sK0,k4_xboole_0(sK1,k1_tarski(sK2)))
      & ~ r2_hidden(sK2,sK0)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2)))
      & ~ r2_hidden(X2,X0)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f4])).

fof(f4,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2)))
      & ~ r2_hidden(X2,X0)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,X1)
       => ( r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2)))
          | r2_hidden(X2,X0) ) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_zfmisc_1)).

fof(f11,plain,(
    ~ r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:25:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.43  % (9923)dis+1_14_awrs=converge:awrsf=256:av=off:bs=on:bsr=on:bce=on:cond=fast:gsp=input_only:gs=on:lcm=predicate:lma=on:nm=4:nwc=1.7:sp=weighted_frequency:urr=on_33 on theBenchmark
% 0.20/0.43  % (9923)Refutation found. Thanks to Tanya!
% 0.20/0.43  % SZS status Theorem for theBenchmark
% 0.20/0.43  % SZS output start Proof for theBenchmark
% 0.20/0.43  fof(f17,plain,(
% 0.20/0.43    $false),
% 0.20/0.43    inference(unit_resulting_resolution,[],[f10,f11,f12,f13])).
% 0.20/0.43  fof(f13,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X0) | r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f7])).
% 0.20/0.43  fof(f7,plain,(
% 0.20/0.43    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2))) | r2_hidden(X2,X0) | ~r1_tarski(X0,X1))),
% 0.20/0.43    inference(flattening,[],[f6])).
% 0.20/0.43  fof(f6,plain,(
% 0.20/0.43    ! [X0,X1,X2] : ((r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2))) | r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f1])).
% 0.20/0.43  fof(f1,axiom,(
% 0.20/0.43    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2))) | r2_hidden(X2,X0)))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l2_zfmisc_1)).
% 0.20/0.43  fof(f12,plain,(
% 0.20/0.43    ~r1_tarski(sK0,k4_xboole_0(sK1,k1_tarski(sK2)))),
% 0.20/0.43    inference(cnf_transformation,[],[f9])).
% 0.20/0.43  fof(f9,plain,(
% 0.20/0.43    ~r1_tarski(sK0,k4_xboole_0(sK1,k1_tarski(sK2))) & ~r2_hidden(sK2,sK0) & r1_tarski(sK0,sK1)),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f8])).
% 0.20/0.43  fof(f8,plain,(
% 0.20/0.43    ? [X0,X1,X2] : (~r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2))) & ~r2_hidden(X2,X0) & r1_tarski(X0,X1)) => (~r1_tarski(sK0,k4_xboole_0(sK1,k1_tarski(sK2))) & ~r2_hidden(sK2,sK0) & r1_tarski(sK0,sK1))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f5,plain,(
% 0.20/0.43    ? [X0,X1,X2] : (~r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2))) & ~r2_hidden(X2,X0) & r1_tarski(X0,X1))),
% 0.20/0.43    inference(flattening,[],[f4])).
% 0.20/0.43  fof(f4,plain,(
% 0.20/0.43    ? [X0,X1,X2] : ((~r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2))) & ~r2_hidden(X2,X0)) & r1_tarski(X0,X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f3])).
% 0.20/0.43  fof(f3,negated_conjecture,(
% 0.20/0.43    ~! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2))) | r2_hidden(X2,X0)))),
% 0.20/0.43    inference(negated_conjecture,[],[f2])).
% 0.20/0.43  fof(f2,conjecture,(
% 0.20/0.43    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2))) | r2_hidden(X2,X0)))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_zfmisc_1)).
% 0.20/0.43  fof(f11,plain,(
% 0.20/0.43    ~r2_hidden(sK2,sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f9])).
% 0.20/0.43  fof(f10,plain,(
% 0.20/0.43    r1_tarski(sK0,sK1)),
% 0.20/0.43    inference(cnf_transformation,[],[f9])).
% 0.20/0.43  % SZS output end Proof for theBenchmark
% 0.20/0.43  % (9923)------------------------------
% 0.20/0.43  % (9923)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (9923)Termination reason: Refutation
% 0.20/0.43  
% 0.20/0.43  % (9923)Memory used [KB]: 5245
% 0.20/0.43  % (9923)Time elapsed: 0.029 s
% 0.20/0.43  % (9923)------------------------------
% 0.20/0.43  % (9923)------------------------------
% 0.20/0.43  % (9902)Success in time 0.079 s
%------------------------------------------------------------------------------
