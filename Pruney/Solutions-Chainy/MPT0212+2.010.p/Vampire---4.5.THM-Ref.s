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
% DateTime   : Thu Dec  3 12:34:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 199 expanded)
%              Number of leaves         :    7 (  49 expanded)
%              Depth                    :   19
%              Number of atoms          :  180 (1173 expanded)
%              Number of equality atoms :   92 ( 669 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f166,plain,(
    $false ),
    inference(resolution,[],[f153,f33])).

fof(f33,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f153,plain,(
    ! [X4] : ~ r2_hidden(k1_xboole_0,k1_tarski(X4)) ),
    inference(subsumption_resolution,[],[f135,f69])).

fof(f69,plain,(
    ! [X2,X3] :
      ( k1_tarski(X3) = k1_tarski(X2)
      | ~ r2_hidden(X2,k1_tarski(X3)) ) ),
    inference(subsumption_resolution,[],[f67,f34])).

fof(f34,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f67,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k1_tarski(X3))
      | k1_tarski(X3) = k1_tarski(X2)
      | X2 != X3 ) ),
    inference(trivial_inequality_removal,[],[f66])).

fof(f66,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k1_tarski(X3))
      | X2 != X2
      | k1_tarski(X3) = k1_tarski(X2)
      | X2 != X3 ) ),
    inference(duplicate_literal_removal,[],[f64])).

fof(f64,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k1_tarski(X3))
      | X2 != X2
      | k1_tarski(X3) = k1_tarski(X2)
      | k1_tarski(X3) = k1_tarski(X2)
      | X2 != X3 ) ),
    inference(superposition,[],[f29,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( sK1(X0,k1_tarski(X1)) = X0
      | k1_tarski(X0) = k1_tarski(X1)
      | X0 != X1 ) ),
    inference(subsumption_resolution,[],[f58,f33])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_tarski(X1))
      | X0 != X1
      | k1_tarski(X0) = k1_tarski(X1)
      | sK1(X0,k1_tarski(X1)) = X0 ) ),
    inference(duplicate_literal_removal,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_tarski(X1))
      | X0 != X1
      | k1_tarski(X0) = k1_tarski(X1)
      | k1_tarski(X0) = k1_tarski(X1)
      | sK1(X0,k1_tarski(X1)) = X0 ) ),
    inference(superposition,[],[f29,f44])).

fof(f44,plain,(
    ! [X2,X3] :
      ( sK1(X2,k1_tarski(X3)) = X3
      | k1_tarski(X3) = k1_tarski(X2)
      | sK1(X2,k1_tarski(X3)) = X2 ) ),
    inference(resolution,[],[f28,f34])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | sK1(X0,X1) = X0
      | k1_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK1(X0,X1),X1)
      | sK1(X0,X1) != X0
      | k1_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f135,plain,(
    ! [X4] :
      ( k1_tarski(k1_xboole_0) != k1_tarski(X4)
      | ~ r2_hidden(k1_xboole_0,k1_tarski(X4)) ) ),
    inference(superposition,[],[f18,f129])).

fof(f129,plain,(
    ! [X2] :
      ( k1_zfmisc_1(k1_xboole_0) = k1_tarski(X2)
      | ~ r2_hidden(k1_xboole_0,k1_tarski(X2)) ) ),
    inference(subsumption_resolution,[],[f128,f115])).

fof(f115,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X2,k1_tarski(X1))
      | X2 = X3
      | ~ r2_hidden(X0,k1_tarski(X3))
      | ~ r2_hidden(X0,k1_tarski(X1)) ) ),
    inference(superposition,[],[f79,f69])).

fof(f79,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X4,k1_tarski(X3))
      | X2 = X4
      | ~ r2_hidden(X3,k1_tarski(X2)) ) ),
    inference(superposition,[],[f34,f69])).

fof(f128,plain,(
    ! [X2] :
      ( ~ r2_hidden(k1_xboole_0,k1_tarski(X2))
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(X2)
      | k1_xboole_0 != X2 ) ),
    inference(subsumption_resolution,[],[f125,f19])).

fof(f19,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f125,plain,(
    ! [X2] :
      ( ~ r2_hidden(k1_xboole_0,k1_tarski(X2))
      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(X2)
      | k1_xboole_0 != X2 ) ),
    inference(duplicate_literal_removal,[],[f122])).

fof(f122,plain,(
    ! [X2] :
      ( ~ r2_hidden(k1_xboole_0,k1_tarski(X2))
      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(X2)
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(X2)
      | k1_xboole_0 != X2 ) ),
    inference(superposition,[],[f25,f93])).

fof(f93,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK0(k1_xboole_0,k1_tarski(X0))
      | k1_tarski(X0) = k1_zfmisc_1(k1_xboole_0)
      | k1_xboole_0 != X0 ) ),
    inference(equality_factoring,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( sK0(k1_xboole_0,k1_tarski(X0)) = X0
      | k1_tarski(X0) = k1_zfmisc_1(k1_xboole_0)
      | k1_xboole_0 = sK0(k1_xboole_0,k1_tarski(X0)) ) ),
    inference(resolution,[],[f39,f21])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f39,plain,(
    ! [X2,X3] :
      ( r1_tarski(sK0(X2,k1_tarski(X3)),X2)
      | k1_tarski(X3) = k1_zfmisc_1(X2)
      | sK0(X2,k1_tarski(X3)) = X3 ) ),
    inference(resolution,[],[f24,f34])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r1_tarski(sK0(X0,X1),X0)
      | k1_zfmisc_1(X0) = X1 ) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK0(X0,X1),X1)
      | ~ r1_tarski(sK0(X0,X1),X0)
      | k1_zfmisc_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f13])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:55:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.51  % (10226)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (10238)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.51  % (10223)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (10231)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.52  % (10223)Refutation not found, incomplete strategy% (10223)------------------------------
% 0.21/0.52  % (10223)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (10223)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (10223)Memory used [KB]: 1663
% 0.21/0.52  % (10223)Time elapsed: 0.097 s
% 0.21/0.52  % (10223)------------------------------
% 0.21/0.52  % (10223)------------------------------
% 0.21/0.52  % (10231)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (10238)Refutation not found, incomplete strategy% (10238)------------------------------
% 0.21/0.52  % (10238)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (10238)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (10238)Memory used [KB]: 10618
% 0.21/0.52  % (10238)Time elapsed: 0.115 s
% 0.21/0.52  % (10238)------------------------------
% 0.21/0.52  % (10238)------------------------------
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f166,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(resolution,[],[f153,f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 0.21/0.52    inference(equality_resolution,[],[f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 0.21/0.52    inference(equality_resolution,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.52    inference(rectify,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.21/0.52  fof(f153,plain,(
% 0.21/0.52    ( ! [X4] : (~r2_hidden(k1_xboole_0,k1_tarski(X4))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f135,f69])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    ( ! [X2,X3] : (k1_tarski(X3) = k1_tarski(X2) | ~r2_hidden(X2,k1_tarski(X3))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f67,f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 0.21/0.52    inference(equality_resolution,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    ( ! [X2,X3] : (~r2_hidden(X2,k1_tarski(X3)) | k1_tarski(X3) = k1_tarski(X2) | X2 != X3) )),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f66])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    ( ! [X2,X3] : (~r2_hidden(X2,k1_tarski(X3)) | X2 != X2 | k1_tarski(X3) = k1_tarski(X2) | X2 != X3) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f64])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    ( ! [X2,X3] : (~r2_hidden(X2,k1_tarski(X3)) | X2 != X2 | k1_tarski(X3) = k1_tarski(X2) | k1_tarski(X3) = k1_tarski(X2) | X2 != X3) )),
% 0.21/0.52    inference(superposition,[],[f29,f59])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    ( ! [X0,X1] : (sK1(X0,k1_tarski(X1)) = X0 | k1_tarski(X0) = k1_tarski(X1) | X0 != X1) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f58,f33])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X1,k1_tarski(X1)) | X0 != X1 | k1_tarski(X0) = k1_tarski(X1) | sK1(X0,k1_tarski(X1)) = X0) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f54])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X1,k1_tarski(X1)) | X0 != X1 | k1_tarski(X0) = k1_tarski(X1) | k1_tarski(X0) = k1_tarski(X1) | sK1(X0,k1_tarski(X1)) = X0) )),
% 0.21/0.52    inference(superposition,[],[f29,f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ( ! [X2,X3] : (sK1(X2,k1_tarski(X3)) = X3 | k1_tarski(X3) = k1_tarski(X2) | sK1(X2,k1_tarski(X3)) = X2) )),
% 0.21/0.52    inference(resolution,[],[f28,f34])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | sK1(X0,X1) = X0 | k1_tarski(X0) = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(sK1(X0,X1),X1) | sK1(X0,X1) != X0 | k1_tarski(X0) = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f135,plain,(
% 0.21/0.52    ( ! [X4] : (k1_tarski(k1_xboole_0) != k1_tarski(X4) | ~r2_hidden(k1_xboole_0,k1_tarski(X4))) )),
% 0.21/0.52    inference(superposition,[],[f18,f129])).
% 0.21/0.52  fof(f129,plain,(
% 0.21/0.52    ( ! [X2] : (k1_zfmisc_1(k1_xboole_0) = k1_tarski(X2) | ~r2_hidden(k1_xboole_0,k1_tarski(X2))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f128,f115])).
% 0.21/0.52  fof(f115,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(X2,k1_tarski(X1)) | X2 = X3 | ~r2_hidden(X0,k1_tarski(X3)) | ~r2_hidden(X0,k1_tarski(X1))) )),
% 0.21/0.52    inference(superposition,[],[f79,f69])).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    ( ! [X4,X2,X3] : (~r2_hidden(X4,k1_tarski(X3)) | X2 = X4 | ~r2_hidden(X3,k1_tarski(X2))) )),
% 0.21/0.52    inference(superposition,[],[f34,f69])).
% 0.21/0.52  fof(f128,plain,(
% 0.21/0.52    ( ! [X2] : (~r2_hidden(k1_xboole_0,k1_tarski(X2)) | k1_zfmisc_1(k1_xboole_0) = k1_tarski(X2) | k1_xboole_0 != X2) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f125,f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.52  fof(f125,plain,(
% 0.21/0.52    ( ! [X2] : (~r2_hidden(k1_xboole_0,k1_tarski(X2)) | ~r1_tarski(k1_xboole_0,k1_xboole_0) | k1_zfmisc_1(k1_xboole_0) = k1_tarski(X2) | k1_xboole_0 != X2) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f122])).
% 0.21/0.52  fof(f122,plain,(
% 0.21/0.52    ( ! [X2] : (~r2_hidden(k1_xboole_0,k1_tarski(X2)) | ~r1_tarski(k1_xboole_0,k1_xboole_0) | k1_zfmisc_1(k1_xboole_0) = k1_tarski(X2) | k1_zfmisc_1(k1_xboole_0) = k1_tarski(X2) | k1_xboole_0 != X2) )),
% 0.21/0.52    inference(superposition,[],[f25,f93])).
% 0.21/0.52  fof(f93,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = sK0(k1_xboole_0,k1_tarski(X0)) | k1_tarski(X0) = k1_zfmisc_1(k1_xboole_0) | k1_xboole_0 != X0) )),
% 0.21/0.52    inference(equality_factoring,[],[f50])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    ( ! [X0] : (sK0(k1_xboole_0,k1_tarski(X0)) = X0 | k1_tarski(X0) = k1_zfmisc_1(k1_xboole_0) | k1_xboole_0 = sK0(k1_xboole_0,k1_tarski(X0))) )),
% 0.21/0.52    inference(resolution,[],[f39,f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X2,X3] : (r1_tarski(sK0(X2,k1_tarski(X3)),X2) | k1_tarski(X3) = k1_zfmisc_1(X2) | sK0(X2,k1_tarski(X3)) = X3) )),
% 0.21/0.52    inference(resolution,[],[f24,f34])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | r1_tarski(sK0(X0,X1),X0) | k1_zfmisc_1(X0) = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.52    inference(rectify,[],[f10])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(sK0(X0,X1),X1) | ~r1_tarski(sK0(X0,X1),X0) | k1_zfmisc_1(X0) = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    k1_zfmisc_1(k1_xboole_0) != k1_tarski(k1_xboole_0)),
% 0.21/0.52    inference(cnf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,plain,(
% 0.21/0.52    k1_zfmisc_1(k1_xboole_0) != k1_tarski(k1_xboole_0)),
% 0.21/0.52    inference(flattening,[],[f7])).
% 0.21/0.52  fof(f7,negated_conjecture,(
% 0.21/0.52    ~k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 0.21/0.52    inference(negated_conjecture,[],[f6])).
% 0.21/0.52  fof(f6,conjecture,(
% 0.21/0.52    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (10231)------------------------------
% 0.21/0.52  % (10231)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (10231)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (10231)Memory used [KB]: 1791
% 0.21/0.52  % (10231)Time elapsed: 0.114 s
% 0.21/0.52  % (10231)------------------------------
% 0.21/0.52  % (10231)------------------------------
% 0.21/0.53  % (10221)Success in time 0.165 s
%------------------------------------------------------------------------------
