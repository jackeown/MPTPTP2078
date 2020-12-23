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
% DateTime   : Thu Dec  3 12:40:12 EST 2020

% Result     : Theorem 1.31s
% Output     : Refutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :   37 (  53 expanded)
%              Number of leaves         :    9 (  15 expanded)
%              Depth                    :   11
%              Number of atoms          :  113 ( 166 expanded)
%              Number of equality atoms :   47 (  59 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f125,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f124])).

fof(f124,plain,(
    k1_tarski(sK1) != k1_tarski(sK1) ),
    inference(superposition,[],[f113,f73])).

fof(f73,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f113,plain,(
    k1_tarski(sK1) != k4_xboole_0(k1_tarski(sK1),k1_xboole_0) ),
    inference(backward_demodulation,[],[f75,f111])).

fof(f111,plain,(
    k1_xboole_0 = k4_xboole_0(k1_tarski(sK1),sK2) ),
    inference(resolution,[],[f107,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l35_zfmisc_1)).

fof(f107,plain,(
    r2_hidden(sK1,sK2) ),
    inference(backward_demodulation,[],[f90,f100])).

fof(f100,plain,(
    sK1 = sK3(k1_tarski(sK1),sK2) ),
    inference(resolution,[],[f89,f85])).

fof(f85,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK5(X0,X1) != X0
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( sK5(X0,X1) = X0
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f35,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK5(X0,X1) != X0
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( sK5(X0,X1) = X0
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f89,plain,(
    r2_hidden(sK3(k1_tarski(sK1),sK2),k1_tarski(sK1)) ),
    inference(resolution,[],[f45,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f45,plain,(
    ~ r1_xboole_0(k1_tarski(sK1),sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( k1_tarski(sK1) != k3_xboole_0(k1_tarski(sK1),sK2)
    & ~ r1_xboole_0(k1_tarski(sK1),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f21,f26])).

fof(f26,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1)
        & ~ r1_xboole_0(k1_tarski(X0),X1) )
   => ( k1_tarski(sK1) != k3_xboole_0(k1_tarski(sK1),sK2)
      & ~ r1_xboole_0(k1_tarski(sK1),sK2) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1)
      & ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1)
        | r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1)
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_zfmisc_1)).

fof(f90,plain,(
    r2_hidden(sK3(k1_tarski(sK1),sK2),sK2) ),
    inference(resolution,[],[f45,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f75,plain,(
    k1_tarski(sK1) != k4_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK1),sK2)) ),
    inference(definition_unfolding,[],[f46,f47])).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f46,plain,(
    k1_tarski(sK1) != k3_xboole_0(k1_tarski(sK1),sK2) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:23:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (28988)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.50  % (29006)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.50  % (29006)Refutation not found, incomplete strategy% (29006)------------------------------
% 0.20/0.50  % (29006)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (29006)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (29006)Memory used [KB]: 6268
% 0.20/0.50  % (29006)Time elapsed: 0.117 s
% 0.20/0.50  % (29006)------------------------------
% 0.20/0.50  % (29006)------------------------------
% 0.20/0.50  % (28995)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.51  % (28998)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.52  % (28996)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.31/0.52  % (28979)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.31/0.52  % (28991)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.31/0.52  % (28981)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.31/0.52  % (28995)Refutation not found, incomplete strategy% (28995)------------------------------
% 1.31/0.52  % (28995)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.52  % (28980)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.31/0.52  % (28995)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.52  
% 1.31/0.52  % (28995)Memory used [KB]: 10618
% 1.31/0.52  % (28995)Time elapsed: 0.127 s
% 1.31/0.52  % (28995)------------------------------
% 1.31/0.52  % (28995)------------------------------
% 1.31/0.52  % (28980)Refutation found. Thanks to Tanya!
% 1.31/0.52  % SZS status Theorem for theBenchmark
% 1.31/0.52  % SZS output start Proof for theBenchmark
% 1.31/0.52  fof(f125,plain,(
% 1.31/0.52    $false),
% 1.31/0.52    inference(trivial_inequality_removal,[],[f124])).
% 1.31/0.52  fof(f124,plain,(
% 1.31/0.52    k1_tarski(sK1) != k1_tarski(sK1)),
% 1.31/0.52    inference(superposition,[],[f113,f73])).
% 1.31/0.52  fof(f73,plain,(
% 1.31/0.52    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.31/0.52    inference(cnf_transformation,[],[f7])).
% 1.31/0.52  fof(f7,axiom,(
% 1.31/0.52    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.31/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.31/0.52  fof(f113,plain,(
% 1.31/0.52    k1_tarski(sK1) != k4_xboole_0(k1_tarski(sK1),k1_xboole_0)),
% 1.31/0.52    inference(backward_demodulation,[],[f75,f111])).
% 1.31/0.52  fof(f111,plain,(
% 1.31/0.52    k1_xboole_0 = k4_xboole_0(k1_tarski(sK1),sK2)),
% 1.31/0.52    inference(resolution,[],[f107,f58])).
% 1.31/0.52  fof(f58,plain,(
% 1.31/0.52    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)) )),
% 1.31/0.52    inference(cnf_transformation,[],[f33])).
% 1.31/0.52  fof(f33,plain,(
% 1.31/0.52    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)))),
% 1.31/0.52    inference(nnf_transformation,[],[f16])).
% 1.31/0.52  fof(f16,axiom,(
% 1.31/0.52    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.31/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l35_zfmisc_1)).
% 1.31/0.52  fof(f107,plain,(
% 1.31/0.52    r2_hidden(sK1,sK2)),
% 1.31/0.52    inference(backward_demodulation,[],[f90,f100])).
% 1.31/0.52  fof(f100,plain,(
% 1.31/0.52    sK1 = sK3(k1_tarski(sK1),sK2)),
% 1.31/0.52    inference(resolution,[],[f89,f85])).
% 1.31/0.52  fof(f85,plain,(
% 1.31/0.52    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 1.31/0.52    inference(equality_resolution,[],[f59])).
% 1.31/0.52  fof(f59,plain,(
% 1.31/0.52    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.31/0.52    inference(cnf_transformation,[],[f37])).
% 1.31/0.52  fof(f37,plain,(
% 1.31/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.31/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f35,f36])).
% 1.31/0.52  fof(f36,plain,(
% 1.31/0.52    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1))))),
% 1.31/0.52    introduced(choice_axiom,[])).
% 1.31/0.52  fof(f35,plain,(
% 1.31/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.31/0.52    inference(rectify,[],[f34])).
% 1.31/0.52  fof(f34,plain,(
% 1.31/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.31/0.52    inference(nnf_transformation,[],[f12])).
% 1.31/0.52  fof(f12,axiom,(
% 1.31/0.52    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.31/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.31/0.52  fof(f89,plain,(
% 1.31/0.52    r2_hidden(sK3(k1_tarski(sK1),sK2),k1_tarski(sK1))),
% 1.31/0.52    inference(resolution,[],[f45,f52])).
% 1.31/0.52  fof(f52,plain,(
% 1.31/0.52    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 1.31/0.52    inference(cnf_transformation,[],[f30])).
% 1.31/0.52  fof(f30,plain,(
% 1.31/0.52    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.31/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f29])).
% 1.31/0.52  fof(f29,plain,(
% 1.31/0.52    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.31/0.52    introduced(choice_axiom,[])).
% 1.31/0.52  fof(f22,plain,(
% 1.31/0.52    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.31/0.52    inference(ennf_transformation,[],[f19])).
% 1.31/0.52  fof(f19,plain,(
% 1.31/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.31/0.52    inference(rectify,[],[f4])).
% 1.31/0.52  fof(f4,axiom,(
% 1.31/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.31/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.31/0.52  fof(f45,plain,(
% 1.31/0.52    ~r1_xboole_0(k1_tarski(sK1),sK2)),
% 1.31/0.52    inference(cnf_transformation,[],[f27])).
% 1.31/0.52  fof(f27,plain,(
% 1.31/0.52    k1_tarski(sK1) != k3_xboole_0(k1_tarski(sK1),sK2) & ~r1_xboole_0(k1_tarski(sK1),sK2)),
% 1.31/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f21,f26])).
% 1.31/0.52  fof(f26,plain,(
% 1.31/0.52    ? [X0,X1] : (k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1) & ~r1_xboole_0(k1_tarski(X0),X1)) => (k1_tarski(sK1) != k3_xboole_0(k1_tarski(sK1),sK2) & ~r1_xboole_0(k1_tarski(sK1),sK2))),
% 1.31/0.52    introduced(choice_axiom,[])).
% 1.31/0.52  fof(f21,plain,(
% 1.31/0.52    ? [X0,X1] : (k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1) & ~r1_xboole_0(k1_tarski(X0),X1))),
% 1.31/0.52    inference(ennf_transformation,[],[f18])).
% 1.31/0.52  fof(f18,negated_conjecture,(
% 1.31/0.52    ~! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1) | r1_xboole_0(k1_tarski(X0),X1))),
% 1.31/0.52    inference(negated_conjecture,[],[f17])).
% 1.31/0.52  fof(f17,conjecture,(
% 1.31/0.52    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1) | r1_xboole_0(k1_tarski(X0),X1))),
% 1.31/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_zfmisc_1)).
% 1.31/0.52  fof(f90,plain,(
% 1.31/0.52    r2_hidden(sK3(k1_tarski(sK1),sK2),sK2)),
% 1.31/0.52    inference(resolution,[],[f45,f53])).
% 1.31/0.52  fof(f53,plain,(
% 1.31/0.52    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK3(X0,X1),X1)) )),
% 1.31/0.52    inference(cnf_transformation,[],[f30])).
% 1.31/0.52  fof(f75,plain,(
% 1.31/0.52    k1_tarski(sK1) != k4_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK1),sK2))),
% 1.31/0.52    inference(definition_unfolding,[],[f46,f47])).
% 1.31/0.52  fof(f47,plain,(
% 1.31/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.31/0.52    inference(cnf_transformation,[],[f9])).
% 1.31/0.52  fof(f9,axiom,(
% 1.31/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.31/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.31/0.52  fof(f46,plain,(
% 1.31/0.52    k1_tarski(sK1) != k3_xboole_0(k1_tarski(sK1),sK2)),
% 1.31/0.52    inference(cnf_transformation,[],[f27])).
% 1.31/0.52  % SZS output end Proof for theBenchmark
% 1.31/0.52  % (28980)------------------------------
% 1.31/0.52  % (28980)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.52  % (28980)Termination reason: Refutation
% 1.31/0.52  
% 1.31/0.52  % (28980)Memory used [KB]: 1791
% 1.31/0.52  % (28980)Time elapsed: 0.126 s
% 1.31/0.52  % (28980)------------------------------
% 1.31/0.52  % (28980)------------------------------
% 1.31/0.52  % (28973)Success in time 0.166 s
%------------------------------------------------------------------------------
