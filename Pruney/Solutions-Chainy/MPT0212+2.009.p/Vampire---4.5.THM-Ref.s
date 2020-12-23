%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 112 expanded)
%              Number of leaves         :    8 (  30 expanded)
%              Depth                    :   14
%              Number of atoms          :  144 ( 456 expanded)
%              Number of equality atoms :   62 ( 176 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f60,plain,(
    $false ),
    inference(subsumption_resolution,[],[f58,f19])).

fof(f19,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f58,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f57,f55])).

fof(f55,plain,(
    k1_xboole_0 = sK0(k1_xboole_0,k2_tarski(k1_xboole_0,k1_xboole_0)) ),
    inference(resolution,[],[f52,f39])).

fof(f39,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k2_tarski(X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f26,f20])).

fof(f20,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f26,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK1(X0,X1) != X0
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( sK1(X0,X1) = X0
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f16])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK1(X0,X1) != X0
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( sK1(X0,X1) = X0
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
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
    inference(rectify,[],[f14])).

fof(f14,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f52,plain,(
    r2_hidden(sK0(k1_xboole_0,k2_tarski(k1_xboole_0,k1_xboole_0)),k2_tarski(k1_xboole_0,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f50,f30])).

fof(f30,plain,(
    k1_zfmisc_1(k1_xboole_0) != k2_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f18,f20])).

fof(f18,plain,(
    k1_zfmisc_1(k1_xboole_0) != k1_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    k1_zfmisc_1(k1_xboole_0) != k1_tarski(k1_xboole_0) ),
    inference(flattening,[],[f7])).

fof(f7,negated_conjecture,(
    k1_zfmisc_1(k1_xboole_0) != k1_tarski(k1_xboole_0) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).

fof(f50,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k2_tarski(k1_xboole_0,k1_xboole_0)
    | r2_hidden(sK0(k1_xboole_0,k2_tarski(k1_xboole_0,k1_xboole_0)),k2_tarski(k1_xboole_0,k1_xboole_0)) ),
    inference(resolution,[],[f49,f38])).

fof(f38,plain,(
    ! [X3] : r2_hidden(X3,k2_tarski(X3,X3)) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_tarski(X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f27,f20])).

fof(f27,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f49,plain,(
    ! [X0] :
      ( ~ r2_hidden(k1_xboole_0,X0)
      | k1_zfmisc_1(k1_xboole_0) = X0
      | r2_hidden(sK0(k1_xboole_0,X0),X0) ) ),
    inference(subsumption_resolution,[],[f48,f19])).

fof(f48,plain,(
    ! [X0] :
      ( ~ r2_hidden(k1_xboole_0,X0)
      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
      | k1_zfmisc_1(k1_xboole_0) = X0
      | r2_hidden(sK0(k1_xboole_0,X0),X0) ) ),
    inference(duplicate_literal_removal,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ r2_hidden(k1_xboole_0,X0)
      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
      | k1_zfmisc_1(k1_xboole_0) = X0
      | r2_hidden(sK0(k1_xboole_0,X0),X0)
      | k1_zfmisc_1(k1_xboole_0) = X0 ) ),
    inference(superposition,[],[f25,f43])).

fof(f43,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK0(k1_xboole_0,X0)
      | r2_hidden(sK0(k1_xboole_0,X0),X0)
      | k1_zfmisc_1(k1_xboole_0) = X0 ) ),
    inference(resolution,[],[f24,f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(sK0(X0,X1),X0)
      | k1_zfmisc_1(X0) = X1
      | r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK0(X0,X1),X0)
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( r1_tarski(sK0(X0,X1),X0)
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f12])).

fof(f12,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK0(X0,X1),X0)
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( r1_tarski(sK0(X0,X1),X0)
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK0(X0,X1),X1)
      | ~ r1_tarski(sK0(X0,X1),X0)
      | k1_zfmisc_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f57,plain,(
    ~ r1_tarski(sK0(k1_xboole_0,k2_tarski(k1_xboole_0,k1_xboole_0)),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f54,f30])).

fof(f54,plain,
    ( ~ r1_tarski(sK0(k1_xboole_0,k2_tarski(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | k1_zfmisc_1(k1_xboole_0) = k2_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f52,f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n007.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 15:07:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.51  % (29770)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.51  % (29762)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.51  % (29762)Refutation not found, incomplete strategy% (29762)------------------------------
% 0.21/0.51  % (29762)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (29762)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (29762)Memory used [KB]: 1663
% 0.21/0.51  % (29762)Time elapsed: 0.062 s
% 0.21/0.51  % (29762)------------------------------
% 0.21/0.51  % (29762)------------------------------
% 0.21/0.51  % (29753)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (29770)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(subsumption_resolution,[],[f58,f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    ~r1_tarski(k1_xboole_0,k1_xboole_0)),
% 0.21/0.51    inference(backward_demodulation,[],[f57,f55])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    k1_xboole_0 = sK0(k1_xboole_0,k2_tarski(k1_xboole_0,k1_xboole_0))),
% 0.21/0.51    inference(resolution,[],[f52,f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ( ! [X0,X3] : (~r2_hidden(X3,k2_tarski(X0,X0)) | X0 = X3) )),
% 0.21/0.51    inference(equality_resolution,[],[f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_tarski(X0,X0) != X1) )),
% 0.21/0.51    inference(definition_unfolding,[],[f26,f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.51    inference(rectify,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.51    inference(nnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    r2_hidden(sK0(k1_xboole_0,k2_tarski(k1_xboole_0,k1_xboole_0)),k2_tarski(k1_xboole_0,k1_xboole_0))),
% 0.21/0.51    inference(subsumption_resolution,[],[f50,f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    k1_zfmisc_1(k1_xboole_0) != k2_tarski(k1_xboole_0,k1_xboole_0)),
% 0.21/0.51    inference(definition_unfolding,[],[f18,f20])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    k1_zfmisc_1(k1_xboole_0) != k1_tarski(k1_xboole_0)),
% 0.21/0.51    inference(cnf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,plain,(
% 0.21/0.51    k1_zfmisc_1(k1_xboole_0) != k1_tarski(k1_xboole_0)),
% 0.21/0.51    inference(flattening,[],[f7])).
% 0.21/0.51  fof(f7,negated_conjecture,(
% 0.21/0.51    ~k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 0.21/0.51    inference(negated_conjecture,[],[f6])).
% 0.21/0.51  fof(f6,conjecture,(
% 0.21/0.51    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    k1_zfmisc_1(k1_xboole_0) = k2_tarski(k1_xboole_0,k1_xboole_0) | r2_hidden(sK0(k1_xboole_0,k2_tarski(k1_xboole_0,k1_xboole_0)),k2_tarski(k1_xboole_0,k1_xboole_0))),
% 0.21/0.51    inference(resolution,[],[f49,f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ( ! [X3] : (r2_hidden(X3,k2_tarski(X3,X3))) )),
% 0.21/0.51    inference(equality_resolution,[],[f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_tarski(X3,X3) != X1) )),
% 0.21/0.51    inference(equality_resolution,[],[f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_tarski(X0,X0) != X1) )),
% 0.21/0.51    inference(definition_unfolding,[],[f27,f20])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(k1_xboole_0,X0) | k1_zfmisc_1(k1_xboole_0) = X0 | r2_hidden(sK0(k1_xboole_0,X0),X0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f48,f19])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(k1_xboole_0,X0) | ~r1_tarski(k1_xboole_0,k1_xboole_0) | k1_zfmisc_1(k1_xboole_0) = X0 | r2_hidden(sK0(k1_xboole_0,X0),X0)) )),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f45])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(k1_xboole_0,X0) | ~r1_tarski(k1_xboole_0,k1_xboole_0) | k1_zfmisc_1(k1_xboole_0) = X0 | r2_hidden(sK0(k1_xboole_0,X0),X0) | k1_zfmisc_1(k1_xboole_0) = X0) )),
% 0.21/0.51    inference(superposition,[],[f25,f43])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = sK0(k1_xboole_0,X0) | r2_hidden(sK0(k1_xboole_0,X0),X0) | k1_zfmisc_1(k1_xboole_0) = X0) )),
% 0.21/0.51    inference(resolution,[],[f24,f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,plain,(
% 0.21/0.51    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(sK0(X0,X1),X0) | k1_zfmisc_1(X0) = X1 | r2_hidden(sK0(X0,X1),X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.51    inference(rectify,[],[f10])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.51    inference(nnf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(sK0(X0,X1),X1) | ~r1_tarski(sK0(X0,X1),X0) | k1_zfmisc_1(X0) = X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ~r1_tarski(sK0(k1_xboole_0,k2_tarski(k1_xboole_0,k1_xboole_0)),k1_xboole_0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f54,f30])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    ~r1_tarski(sK0(k1_xboole_0,k2_tarski(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | k1_zfmisc_1(k1_xboole_0) = k2_tarski(k1_xboole_0,k1_xboole_0)),
% 0.21/0.51    inference(resolution,[],[f52,f25])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (29770)------------------------------
% 0.21/0.51  % (29770)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (29770)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (29770)Memory used [KB]: 6268
% 0.21/0.51  % (29770)Time elapsed: 0.065 s
% 0.21/0.51  % (29770)------------------------------
% 0.21/0.51  % (29770)------------------------------
% 0.21/0.52  % (29747)Success in time 0.153 s
%------------------------------------------------------------------------------
