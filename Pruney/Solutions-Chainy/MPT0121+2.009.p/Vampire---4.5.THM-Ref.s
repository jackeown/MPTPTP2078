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
% DateTime   : Thu Dec  3 12:32:57 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 151 expanded)
%              Number of leaves         :    6 (  40 expanded)
%              Depth                    :   20
%              Number of atoms          :  122 ( 604 expanded)
%              Number of equality atoms :   16 (  39 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f320,plain,(
    $false ),
    inference(subsumption_resolution,[],[f319,f16])).

fof(f16,plain,(
    r1_xboole_0(sK0,sK3) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3)
    & r1_xboole_0(sK2,sK3)
    & r1_xboole_0(sK1,sK3)
    & r1_xboole_0(sK0,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3)
        & r1_xboole_0(X2,X3)
        & r1_xboole_0(X1,X3)
        & r1_xboole_0(X0,X3) )
   => ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3)
      & r1_xboole_0(sK2,sK3)
      & r1_xboole_0(sK1,sK3)
      & r1_xboole_0(sK0,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3)
      & r1_xboole_0(X2,X3)
      & r1_xboole_0(X1,X3)
      & r1_xboole_0(X0,X3) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3)
      & r1_xboole_0(X2,X3)
      & r1_xboole_0(X1,X3)
      & r1_xboole_0(X0,X3) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X3)
          & r1_xboole_0(X1,X3)
          & r1_xboole_0(X0,X3) )
       => r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        & r1_xboole_0(X1,X3)
        & r1_xboole_0(X0,X3) )
     => r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_xboole_1)).

fof(f319,plain,(
    ~ r1_xboole_0(sK0,sK3) ),
    inference(resolution,[],[f302,f43])).

fof(f43,plain,(
    ! [X2,X3] :
      ( r1_xboole_0(X3,X2)
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(duplicate_literal_removal,[],[f42])).

fof(f42,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(X2,X3)
      | r1_xboole_0(X3,X2)
      | r1_xboole_0(X3,X2) ) ),
    inference(resolution,[],[f29,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f10,f13])).

fof(f13,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
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

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X1,X2),X0)
      | ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X2) ) ),
    inference(resolution,[],[f23,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f302,plain,(
    ~ r1_xboole_0(sK3,sK0) ),
    inference(subsumption_resolution,[],[f301,f17])).

fof(f17,plain,(
    r1_xboole_0(sK1,sK3) ),
    inference(cnf_transformation,[],[f12])).

fof(f301,plain,
    ( ~ r1_xboole_0(sK3,sK0)
    | ~ r1_xboole_0(sK1,sK3) ),
    inference(resolution,[],[f277,f43])).

fof(f277,plain,
    ( ~ r1_xboole_0(sK3,sK1)
    | ~ r1_xboole_0(sK3,sK0) ),
    inference(subsumption_resolution,[],[f276,f18])).

fof(f18,plain,(
    r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f12])).

fof(f276,plain,
    ( ~ r1_xboole_0(sK3,sK0)
    | ~ r1_xboole_0(sK3,sK1)
    | ~ r1_xboole_0(sK2,sK3) ),
    inference(resolution,[],[f260,f43])).

fof(f260,plain,
    ( ~ r1_xboole_0(sK3,sK2)
    | ~ r1_xboole_0(sK3,sK0)
    | ~ r1_xboole_0(sK3,sK1) ),
    inference(trivial_inequality_removal,[],[f259])).

fof(f259,plain,
    ( sK3 != sK3
    | ~ r1_xboole_0(sK3,sK0)
    | ~ r1_xboole_0(sK3,sK2)
    | ~ r1_xboole_0(sK3,sK1) ),
    inference(superposition,[],[f242,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f242,plain,
    ( sK3 != k4_xboole_0(sK3,sK1)
    | ~ r1_xboole_0(sK3,sK0)
    | ~ r1_xboole_0(sK3,sK2) ),
    inference(trivial_inequality_removal,[],[f241])).

fof(f241,plain,
    ( sK3 != sK3
    | sK3 != k4_xboole_0(sK3,sK1)
    | ~ r1_xboole_0(sK3,sK0)
    | ~ r1_xboole_0(sK3,sK2) ),
    inference(superposition,[],[f141,f24])).

fof(f141,plain,
    ( sK3 != k4_xboole_0(sK3,sK2)
    | sK3 != k4_xboole_0(sK3,sK1)
    | ~ r1_xboole_0(sK3,sK0) ),
    inference(resolution,[],[f137,f54])).

fof(f54,plain,(
    ! [X8,X7,X9] :
      ( r1_xboole_0(X7,k2_xboole_0(X8,X9))
      | k4_xboole_0(X7,X9) != X7
      | ~ r1_xboole_0(X7,X8) ) ),
    inference(superposition,[],[f25,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f26,f24])).

fof(f26,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f137,plain,
    ( ~ r1_xboole_0(sK3,k2_xboole_0(sK0,sK1))
    | sK3 != k4_xboole_0(sK3,sK2) ),
    inference(resolution,[],[f54,f49])).

fof(f49,plain,(
    ~ r1_xboole_0(sK3,k2_xboole_0(k2_xboole_0(sK0,sK1),sK2)) ),
    inference(resolution,[],[f43,f19])).

fof(f19,plain,(
    ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:44:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (24839)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.48  % (24842)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (24843)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.49  % (24840)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.49  % (24850)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.49  % (24841)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.50  % (24849)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.50  % (24844)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.50  % (24838)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.51  % (24851)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.51  % (24847)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.51  % (24848)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.52  % (24840)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f320,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(subsumption_resolution,[],[f319,f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    r1_xboole_0(sK0,sK3)),
% 0.22/0.52    inference(cnf_transformation,[],[f12])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    ~r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3) & r1_xboole_0(sK2,sK3) & r1_xboole_0(sK1,sK3) & r1_xboole_0(sK0,sK3)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f11])).
% 0.22/0.52  fof(f11,plain,(
% 0.22/0.52    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) & r1_xboole_0(X2,X3) & r1_xboole_0(X1,X3) & r1_xboole_0(X0,X3)) => (~r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3) & r1_xboole_0(sK2,sK3) & r1_xboole_0(sK1,sK3) & r1_xboole_0(sK0,sK3))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f9,plain,(
% 0.22/0.52    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) & r1_xboole_0(X2,X3) & r1_xboole_0(X1,X3) & r1_xboole_0(X0,X3))),
% 0.22/0.52    inference(flattening,[],[f8])).
% 0.22/0.52  fof(f8,plain,(
% 0.22/0.52    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) & (r1_xboole_0(X2,X3) & r1_xboole_0(X1,X3) & r1_xboole_0(X0,X3)))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) & r1_xboole_0(X1,X3) & r1_xboole_0(X0,X3)) => r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3))),
% 0.22/0.52    inference(negated_conjecture,[],[f5])).
% 0.22/0.52  fof(f5,conjecture,(
% 0.22/0.52    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) & r1_xboole_0(X1,X3) & r1_xboole_0(X0,X3)) => r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_xboole_1)).
% 0.22/0.52  fof(f319,plain,(
% 0.22/0.52    ~r1_xboole_0(sK0,sK3)),
% 0.22/0.52    inference(resolution,[],[f302,f43])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    ( ! [X2,X3] : (r1_xboole_0(X3,X2) | ~r1_xboole_0(X2,X3)) )),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f42])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    ( ! [X2,X3] : (~r1_xboole_0(X2,X3) | r1_xboole_0(X3,X2) | r1_xboole_0(X3,X2)) )),
% 0.22/0.52    inference(resolution,[],[f29,f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f10,f13])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f10,plain,(
% 0.22/0.52    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.52    inference(ennf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,plain,(
% 0.22/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.52    inference(rectify,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X1,X2),X0) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X2)) )),
% 0.22/0.52    inference(resolution,[],[f23,f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f14])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f14])).
% 0.22/0.52  fof(f302,plain,(
% 0.22/0.52    ~r1_xboole_0(sK3,sK0)),
% 0.22/0.52    inference(subsumption_resolution,[],[f301,f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    r1_xboole_0(sK1,sK3)),
% 0.22/0.52    inference(cnf_transformation,[],[f12])).
% 0.22/0.52  fof(f301,plain,(
% 0.22/0.52    ~r1_xboole_0(sK3,sK0) | ~r1_xboole_0(sK1,sK3)),
% 0.22/0.52    inference(resolution,[],[f277,f43])).
% 0.22/0.52  fof(f277,plain,(
% 0.22/0.52    ~r1_xboole_0(sK3,sK1) | ~r1_xboole_0(sK3,sK0)),
% 0.22/0.52    inference(subsumption_resolution,[],[f276,f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    r1_xboole_0(sK2,sK3)),
% 0.22/0.52    inference(cnf_transformation,[],[f12])).
% 0.22/0.52  fof(f276,plain,(
% 0.22/0.52    ~r1_xboole_0(sK3,sK0) | ~r1_xboole_0(sK3,sK1) | ~r1_xboole_0(sK2,sK3)),
% 0.22/0.52    inference(resolution,[],[f260,f43])).
% 0.22/0.53  fof(f260,plain,(
% 0.22/0.53    ~r1_xboole_0(sK3,sK2) | ~r1_xboole_0(sK3,sK0) | ~r1_xboole_0(sK3,sK1)),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f259])).
% 0.22/0.53  fof(f259,plain,(
% 0.22/0.53    sK3 != sK3 | ~r1_xboole_0(sK3,sK0) | ~r1_xboole_0(sK3,sK2) | ~r1_xboole_0(sK3,sK1)),
% 0.22/0.53    inference(superposition,[],[f242,f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.53    inference(nnf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.22/0.53  fof(f242,plain,(
% 0.22/0.53    sK3 != k4_xboole_0(sK3,sK1) | ~r1_xboole_0(sK3,sK0) | ~r1_xboole_0(sK3,sK2)),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f241])).
% 0.22/0.53  fof(f241,plain,(
% 0.22/0.53    sK3 != sK3 | sK3 != k4_xboole_0(sK3,sK1) | ~r1_xboole_0(sK3,sK0) | ~r1_xboole_0(sK3,sK2)),
% 0.22/0.53    inference(superposition,[],[f141,f24])).
% 0.22/0.53  fof(f141,plain,(
% 0.22/0.53    sK3 != k4_xboole_0(sK3,sK2) | sK3 != k4_xboole_0(sK3,sK1) | ~r1_xboole_0(sK3,sK0)),
% 0.22/0.53    inference(resolution,[],[f137,f54])).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    ( ! [X8,X7,X9] : (r1_xboole_0(X7,k2_xboole_0(X8,X9)) | k4_xboole_0(X7,X9) != X7 | ~r1_xboole_0(X7,X8)) )),
% 0.22/0.53    inference(superposition,[],[f25,f33])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.53    inference(superposition,[],[f26,f24])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f137,plain,(
% 0.22/0.53    ~r1_xboole_0(sK3,k2_xboole_0(sK0,sK1)) | sK3 != k4_xboole_0(sK3,sK2)),
% 0.22/0.53    inference(resolution,[],[f54,f49])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    ~r1_xboole_0(sK3,k2_xboole_0(k2_xboole_0(sK0,sK1),sK2))),
% 0.22/0.53    inference(resolution,[],[f43,f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ~r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3)),
% 0.22/0.53    inference(cnf_transformation,[],[f12])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (24840)------------------------------
% 0.22/0.53  % (24840)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (24840)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (24840)Memory used [KB]: 1791
% 0.22/0.53  % (24840)Time elapsed: 0.079 s
% 0.22/0.53  % (24840)------------------------------
% 0.22/0.53  % (24840)------------------------------
% 0.22/0.53  % (24836)Success in time 0.163 s
%------------------------------------------------------------------------------
