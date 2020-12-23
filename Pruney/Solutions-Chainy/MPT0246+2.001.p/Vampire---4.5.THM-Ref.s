%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:45 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 195 expanded)
%              Number of leaves         :    8 (  49 expanded)
%              Depth                    :   20
%              Number of atoms          :  140 ( 674 expanded)
%              Number of equality atoms :   49 ( 250 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f146,plain,(
    $false ),
    inference(subsumption_resolution,[],[f145,f28])).

fof(f28,plain,(
    sK0 != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ! [X2] :
        ( sK1 = X2
        | ~ r2_hidden(X2,sK0) )
    & k1_xboole_0 != sK0
    & sK0 != k1_tarski(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f21])).

fof(f21,plain,
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

fof(f15,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ~ r2_hidden(X2,X0) )
      & k1_xboole_0 != X0
      & k1_tarski(X1) != X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ~ ( X1 != X2
                & r2_hidden(X2,X0) )
          & k1_xboole_0 != X0
          & k1_tarski(X1) != X0 ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).

fof(f145,plain,(
    sK0 = k1_tarski(sK1) ),
    inference(subsumption_resolution,[],[f143,f57])).

fof(f57,plain,(
    r2_hidden(sK1,sK0) ),
    inference(subsumption_resolution,[],[f56,f29])).

fof(f29,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f22])).

fof(f56,plain,
    ( r2_hidden(sK1,sK0)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f55,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

fof(f55,plain,(
    ! [X1] :
      ( r1_tarski(sK0,k4_xboole_0(X1,sK0))
      | r2_hidden(sK1,sK0) ) ),
    inference(superposition,[],[f39,f53])).

fof(f53,plain,(
    ! [X0] : sK1 = sK2(sK0,k4_xboole_0(X0,sK0)) ),
    inference(subsumption_resolution,[],[f52,f29])).

fof(f52,plain,(
    ! [X0] :
      ( sK1 = sK2(sK0,k4_xboole_0(X0,sK0))
      | k1_xboole_0 = sK0 ) ),
    inference(resolution,[],[f48,f36])).

fof(f48,plain,(
    ! [X0] :
      ( r1_tarski(sK0,X0)
      | sK1 = sK2(sK0,X0) ) ),
    inference(resolution,[],[f39,f30])).

fof(f30,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK0)
      | sK1 = X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f143,plain,
    ( ~ r2_hidden(sK1,sK0)
    | sK0 = k1_tarski(sK1) ),
    inference(resolution,[],[f142,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1)
      | k1_tarski(X0) = X1 ) ),
    inference(resolution,[],[f60,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | ~ r2_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
     => ~ r2_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).

fof(f60,plain,(
    ! [X2,X3] :
      ( r2_xboole_0(k1_tarski(X2),X3)
      | k1_tarski(X2) = X3
      | ~ r2_hidden(X2,X3) ) ),
    inference(resolution,[],[f37,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_zfmisc_1)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f142,plain,(
    r2_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(subsumption_resolution,[],[f141,f28])).

fof(f141,plain,
    ( sK0 = k1_tarski(sK1)
    | r2_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(resolution,[],[f137,f37])).

fof(f137,plain,(
    r1_tarski(sK0,k1_tarski(sK1)) ),
    inference(subsumption_resolution,[],[f135,f51])).

fof(f51,plain,(
    ! [X0] : r2_hidden(X0,k1_tarski(X0)) ),
    inference(resolution,[],[f50,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f50,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f40,f39])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f135,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK1))
    | r1_tarski(sK0,k1_tarski(sK1)) ),
    inference(superposition,[],[f40,f133])).

fof(f133,plain,(
    sK1 = sK2(sK0,k1_tarski(sK1)) ),
    inference(subsumption_resolution,[],[f130,f28])).

fof(f130,plain,
    ( sK0 = k1_tarski(sK1)
    | sK1 = sK2(sK0,k1_tarski(sK1)) ),
    inference(resolution,[],[f84,f57])).

fof(f84,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK0)
      | sK0 = k1_tarski(X2)
      | sK1 = sK2(sK0,k1_tarski(X2)) ) ),
    inference(duplicate_literal_removal,[],[f83])).

fof(f83,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK0)
      | sK0 = k1_tarski(X2)
      | sK0 = k1_tarski(X2)
      | sK1 = sK2(sK0,k1_tarski(X2)) ) ),
    inference(resolution,[],[f76,f62])).

fof(f62,plain,(
    ! [X5] :
      ( r2_xboole_0(sK0,X5)
      | sK0 = X5
      | sK1 = sK2(sK0,X5) ) ),
    inference(resolution,[],[f37,f48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.12/0.32  % Computer   : n010.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 18:41:59 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.18/0.45  % (24128)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.18/0.46  % (24136)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.18/0.46  % (24131)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.18/0.47  % (24144)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.18/0.48  % (24123)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.18/0.49  % (24131)Refutation found. Thanks to Tanya!
% 0.18/0.49  % SZS status Theorem for theBenchmark
% 0.18/0.49  % (24147)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.18/0.49  % SZS output start Proof for theBenchmark
% 0.18/0.49  fof(f146,plain,(
% 0.18/0.49    $false),
% 0.18/0.49    inference(subsumption_resolution,[],[f145,f28])).
% 0.18/0.49  fof(f28,plain,(
% 0.18/0.49    sK0 != k1_tarski(sK1)),
% 0.18/0.49    inference(cnf_transformation,[],[f22])).
% 0.18/0.49  fof(f22,plain,(
% 0.18/0.49    ! [X2] : (sK1 = X2 | ~r2_hidden(X2,sK0)) & k1_xboole_0 != sK0 & sK0 != k1_tarski(sK1)),
% 0.18/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f21])).
% 0.18/0.49  fof(f21,plain,(
% 0.18/0.49    ? [X0,X1] : (! [X2] : (X1 = X2 | ~r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0) => (! [X2] : (sK1 = X2 | ~r2_hidden(X2,sK0)) & k1_xboole_0 != sK0 & sK0 != k1_tarski(sK1))),
% 0.18/0.49    introduced(choice_axiom,[])).
% 0.18/0.49  fof(f15,plain,(
% 0.18/0.49    ? [X0,X1] : (! [X2] : (X1 = X2 | ~r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 0.18/0.49    inference(ennf_transformation,[],[f13])).
% 0.18/0.49  fof(f13,negated_conjecture,(
% 0.18/0.49    ~! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 0.18/0.49    inference(negated_conjecture,[],[f12])).
% 0.18/0.49  fof(f12,conjecture,(
% 0.18/0.49    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 0.18/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).
% 0.18/0.49  fof(f145,plain,(
% 0.18/0.49    sK0 = k1_tarski(sK1)),
% 0.18/0.49    inference(subsumption_resolution,[],[f143,f57])).
% 0.18/0.49  fof(f57,plain,(
% 0.18/0.49    r2_hidden(sK1,sK0)),
% 0.18/0.49    inference(subsumption_resolution,[],[f56,f29])).
% 0.18/0.49  fof(f29,plain,(
% 0.18/0.49    k1_xboole_0 != sK0),
% 0.18/0.49    inference(cnf_transformation,[],[f22])).
% 0.18/0.49  fof(f56,plain,(
% 0.18/0.49    r2_hidden(sK1,sK0) | k1_xboole_0 = sK0),
% 0.18/0.49    inference(resolution,[],[f55,f36])).
% 0.18/0.49  fof(f36,plain,(
% 0.18/0.49    ( ! [X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X0)) | k1_xboole_0 = X0) )),
% 0.18/0.49    inference(cnf_transformation,[],[f17])).
% 0.18/0.49  fof(f17,plain,(
% 0.18/0.49    ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 0.18/0.49    inference(ennf_transformation,[],[f4])).
% 0.18/0.49  fof(f4,axiom,(
% 0.18/0.49    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 0.18/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).
% 0.18/0.49  fof(f55,plain,(
% 0.18/0.49    ( ! [X1] : (r1_tarski(sK0,k4_xboole_0(X1,sK0)) | r2_hidden(sK1,sK0)) )),
% 0.18/0.49    inference(superposition,[],[f39,f53])).
% 0.18/0.49  fof(f53,plain,(
% 0.18/0.49    ( ! [X0] : (sK1 = sK2(sK0,k4_xboole_0(X0,sK0))) )),
% 0.18/0.49    inference(subsumption_resolution,[],[f52,f29])).
% 0.18/0.49  fof(f52,plain,(
% 0.18/0.49    ( ! [X0] : (sK1 = sK2(sK0,k4_xboole_0(X0,sK0)) | k1_xboole_0 = sK0) )),
% 0.18/0.49    inference(resolution,[],[f48,f36])).
% 0.18/0.49  fof(f48,plain,(
% 0.18/0.49    ( ! [X0] : (r1_tarski(sK0,X0) | sK1 = sK2(sK0,X0)) )),
% 0.18/0.49    inference(resolution,[],[f39,f30])).
% 0.18/0.49  fof(f30,plain,(
% 0.18/0.49    ( ! [X2] : (~r2_hidden(X2,sK0) | sK1 = X2) )),
% 0.18/0.49    inference(cnf_transformation,[],[f22])).
% 0.18/0.49  fof(f39,plain,(
% 0.18/0.49    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.18/0.49    inference(cnf_transformation,[],[f26])).
% 0.18/0.49  fof(f26,plain,(
% 0.18/0.49    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.18/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f25])).
% 0.18/0.49  fof(f25,plain,(
% 0.18/0.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.18/0.49    introduced(choice_axiom,[])).
% 0.18/0.49  fof(f24,plain,(
% 0.18/0.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.18/0.49    inference(rectify,[],[f23])).
% 0.18/0.49  fof(f23,plain,(
% 0.18/0.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.18/0.49    inference(nnf_transformation,[],[f20])).
% 0.18/0.49  fof(f20,plain,(
% 0.18/0.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.18/0.49    inference(ennf_transformation,[],[f2])).
% 0.18/0.49  fof(f2,axiom,(
% 0.18/0.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.18/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.18/0.49  fof(f143,plain,(
% 0.18/0.49    ~r2_hidden(sK1,sK0) | sK0 = k1_tarski(sK1)),
% 0.18/0.49    inference(resolution,[],[f142,f76])).
% 0.18/0.49  fof(f76,plain,(
% 0.18/0.49    ( ! [X0,X1] : (~r2_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1) | k1_tarski(X0) = X1) )),
% 0.18/0.49    inference(resolution,[],[f60,f35])).
% 0.18/0.49  fof(f35,plain,(
% 0.18/0.49    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | ~r2_xboole_0(X1,X0)) )),
% 0.18/0.49    inference(cnf_transformation,[],[f16])).
% 0.18/0.49  fof(f16,plain,(
% 0.18/0.49    ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r2_xboole_0(X0,X1))),
% 0.18/0.49    inference(ennf_transformation,[],[f1])).
% 0.18/0.49  fof(f1,axiom,(
% 0.18/0.49    ! [X0,X1] : (r2_xboole_0(X0,X1) => ~r2_xboole_0(X1,X0))),
% 0.18/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).
% 0.18/0.49  fof(f60,plain,(
% 0.18/0.49    ( ! [X2,X3] : (r2_xboole_0(k1_tarski(X2),X3) | k1_tarski(X2) = X3 | ~r2_hidden(X2,X3)) )),
% 0.18/0.49    inference(resolution,[],[f37,f42])).
% 0.18/0.49  fof(f42,plain,(
% 0.18/0.49    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.18/0.49    inference(cnf_transformation,[],[f27])).
% 0.18/0.49  fof(f27,plain,(
% 0.18/0.49    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.18/0.49    inference(nnf_transformation,[],[f11])).
% 0.18/0.49  fof(f11,axiom,(
% 0.18/0.49    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.18/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_zfmisc_1)).
% 0.18/0.49  fof(f37,plain,(
% 0.18/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.18/0.49    inference(cnf_transformation,[],[f19])).
% 0.18/0.49  fof(f19,plain,(
% 0.18/0.49    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 0.18/0.49    inference(flattening,[],[f18])).
% 0.18/0.49  fof(f18,plain,(
% 0.18/0.49    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 0.18/0.49    inference(ennf_transformation,[],[f14])).
% 0.18/0.49  fof(f14,plain,(
% 0.18/0.49    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 0.18/0.49    inference(unused_predicate_definition_removal,[],[f3])).
% 0.18/0.49  fof(f3,axiom,(
% 0.18/0.49    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.18/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.18/0.49  fof(f142,plain,(
% 0.18/0.49    r2_xboole_0(sK0,k1_tarski(sK1))),
% 0.18/0.49    inference(subsumption_resolution,[],[f141,f28])).
% 0.18/0.49  fof(f141,plain,(
% 0.18/0.49    sK0 = k1_tarski(sK1) | r2_xboole_0(sK0,k1_tarski(sK1))),
% 0.18/0.49    inference(resolution,[],[f137,f37])).
% 0.18/0.49  fof(f137,plain,(
% 0.18/0.49    r1_tarski(sK0,k1_tarski(sK1))),
% 0.18/0.49    inference(subsumption_resolution,[],[f135,f51])).
% 0.18/0.49  fof(f51,plain,(
% 0.18/0.49    ( ! [X0] : (r2_hidden(X0,k1_tarski(X0))) )),
% 0.18/0.49    inference(resolution,[],[f50,f41])).
% 0.18/0.49  fof(f41,plain,(
% 0.18/0.49    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.18/0.49    inference(cnf_transformation,[],[f27])).
% 0.18/0.49  fof(f50,plain,(
% 0.18/0.49    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.18/0.49    inference(duplicate_literal_removal,[],[f49])).
% 0.18/0.49  fof(f49,plain,(
% 0.18/0.49    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 0.18/0.49    inference(resolution,[],[f40,f39])).
% 0.18/0.49  fof(f40,plain,(
% 0.18/0.49    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.18/0.49    inference(cnf_transformation,[],[f26])).
% 0.18/0.49  fof(f135,plain,(
% 0.18/0.49    ~r2_hidden(sK1,k1_tarski(sK1)) | r1_tarski(sK0,k1_tarski(sK1))),
% 0.18/0.49    inference(superposition,[],[f40,f133])).
% 0.18/0.49  fof(f133,plain,(
% 0.18/0.49    sK1 = sK2(sK0,k1_tarski(sK1))),
% 0.18/0.49    inference(subsumption_resolution,[],[f130,f28])).
% 0.18/0.49  fof(f130,plain,(
% 0.18/0.49    sK0 = k1_tarski(sK1) | sK1 = sK2(sK0,k1_tarski(sK1))),
% 0.18/0.49    inference(resolution,[],[f84,f57])).
% 0.18/0.49  fof(f84,plain,(
% 0.18/0.49    ( ! [X2] : (~r2_hidden(X2,sK0) | sK0 = k1_tarski(X2) | sK1 = sK2(sK0,k1_tarski(X2))) )),
% 0.18/0.49    inference(duplicate_literal_removal,[],[f83])).
% 0.18/0.49  fof(f83,plain,(
% 0.18/0.49    ( ! [X2] : (~r2_hidden(X2,sK0) | sK0 = k1_tarski(X2) | sK0 = k1_tarski(X2) | sK1 = sK2(sK0,k1_tarski(X2))) )),
% 0.18/0.49    inference(resolution,[],[f76,f62])).
% 0.18/0.49  fof(f62,plain,(
% 0.18/0.49    ( ! [X5] : (r2_xboole_0(sK0,X5) | sK0 = X5 | sK1 = sK2(sK0,X5)) )),
% 0.18/0.49    inference(resolution,[],[f37,f48])).
% 0.18/0.49  % SZS output end Proof for theBenchmark
% 0.18/0.49  % (24131)------------------------------
% 0.18/0.49  % (24131)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.49  % (24131)Termination reason: Refutation
% 0.18/0.49  
% 0.18/0.49  % (24131)Memory used [KB]: 6268
% 0.18/0.49  % (24131)Time elapsed: 0.103 s
% 0.18/0.49  % (24131)------------------------------
% 0.18/0.49  % (24131)------------------------------
% 0.18/0.49  % (24121)Success in time 0.162 s
%------------------------------------------------------------------------------
