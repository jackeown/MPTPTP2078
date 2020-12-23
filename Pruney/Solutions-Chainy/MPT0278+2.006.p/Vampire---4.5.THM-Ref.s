%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   36 ( 107 expanded)
%              Number of leaves         :    6 (  28 expanded)
%              Depth                    :   10
%              Number of atoms          :  114 ( 418 expanded)
%              Number of equality atoms :    9 (  24 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f135,plain,(
    $false ),
    inference(subsumption_resolution,[],[f133,f74])).

fof(f74,plain,(
    r2_hidden(sK3(sK3(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),sK1),sK3(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))) ),
    inference(resolution,[],[f68,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f17])).

% (7924)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f68,plain,(
    ~ r1_tarski(sK3(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),sK1) ),
    inference(resolution,[],[f33,f28])).

fof(f28,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK2(X0,X1),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r1_tarski(sK2(X0,X1),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f12,f13])).

fof(f13,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK2(X0,X1),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( r1_tarski(sK2(X0,X1),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
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
    inference(rectify,[],[f11])).

fof(f11,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f33,plain,(
    ~ r2_hidden(sK3(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f20,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f20,plain,(
    ~ r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( ~ r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f9])).

fof(f9,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

% (7931)Refutation not found, incomplete strategy% (7931)------------------------------
% (7931)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (7931)Termination reason: Refutation not found, incomplete strategy

% (7931)Memory used [KB]: 10618
% (7931)Time elapsed: 0.105 s
% (7931)------------------------------
% (7931)------------------------------
fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,X1)
       => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(f133,plain,(
    ~ r2_hidden(sK3(sK3(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),sK1),sK3(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))) ),
    inference(resolution,[],[f62,f84])).

fof(f84,plain,(
    ~ r2_hidden(sK3(sK3(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),sK1),sK0) ),
    inference(resolution,[],[f45,f68])).

fof(f45,plain,(
    ! [X3] :
      ( r1_tarski(X3,sK1)
      | ~ r2_hidden(sK3(X3,sK1),sK0) ) ),
    inference(resolution,[],[f30,f27])).

fof(f30,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f19,f25])).

fof(f25,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f62,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK0)
      | ~ r2_hidden(X0,sK3(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))) ) ),
    inference(resolution,[],[f56,f25])).

fof(f56,plain,(
    r1_tarski(sK3(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),sK0) ),
    inference(resolution,[],[f32,f29])).

fof(f29,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f32,plain,(
    r2_hidden(sK3(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f20,f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:28:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.53  % (7921)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (7933)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (7922)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (7931)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (7921)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % (7929)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (7940)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (7938)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (7927)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f135,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(subsumption_resolution,[],[f133,f74])).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    r2_hidden(sK3(sK3(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),sK1),sK3(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))),
% 0.21/0.53    inference(resolution,[],[f68,f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f17])).
% 0.21/0.54  % (7924)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.54    inference(rectify,[],[f15])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.54    inference(nnf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,plain,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.54  fof(f68,plain,(
% 0.21/0.54    ~r1_tarski(sK3(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),sK1)),
% 0.21/0.54    inference(resolution,[],[f33,f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 0.21/0.54    inference(equality_resolution,[],[f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f12,f13])).
% 0.21/0.54  fof(f13,plain,(
% 0.21/0.54    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f12,plain,(
% 0.21/0.54    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.54    inference(rectify,[],[f11])).
% 0.21/0.54  fof(f11,plain,(
% 0.21/0.54    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.54    inference(nnf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ~r2_hidden(sK3(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),k1_zfmisc_1(sK1))),
% 0.21/0.54    inference(resolution,[],[f20,f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK3(X0,X1),X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f18])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ~r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))),
% 0.21/0.54    inference(cnf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,plain,(
% 0.21/0.54    ~r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)) & r1_tarski(sK0,sK1)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f9])).
% 0.21/0.54  fof(f9,plain,(
% 0.21/0.54    ? [X0,X1] : (~r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) & r1_tarski(X0,X1)) => (~r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)) & r1_tarski(sK0,sK1))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f7,plain,(
% 0.21/0.54    ? [X0,X1] : (~r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) & r1_tarski(X0,X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f6])).
% 0.21/0.54  % (7931)Refutation not found, incomplete strategy% (7931)------------------------------
% 0.21/0.54  % (7931)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (7931)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (7931)Memory used [KB]: 10618
% 0.21/0.54  % (7931)Time elapsed: 0.105 s
% 0.21/0.54  % (7931)------------------------------
% 0.21/0.54  % (7931)------------------------------
% 0.21/0.54  fof(f6,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))),
% 0.21/0.54    inference(negated_conjecture,[],[f5])).
% 0.21/0.54  fof(f5,conjecture,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).
% 0.21/0.54  fof(f133,plain,(
% 0.21/0.54    ~r2_hidden(sK3(sK3(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),sK1),sK3(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))),
% 0.21/0.54    inference(resolution,[],[f62,f84])).
% 0.21/0.54  fof(f84,plain,(
% 0.21/0.54    ~r2_hidden(sK3(sK3(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),sK1),sK0)),
% 0.21/0.54    inference(resolution,[],[f45,f68])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ( ! [X3] : (r1_tarski(X3,sK1) | ~r2_hidden(sK3(X3,sK1),sK0)) )),
% 0.21/0.54    inference(resolution,[],[f30,f27])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0)) )),
% 0.21/0.54    inference(resolution,[],[f19,f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f18])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    r1_tarski(sK0,sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f10])).
% 0.21/0.54  fof(f62,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(X0,sK0) | ~r2_hidden(X0,sK3(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))) )),
% 0.21/0.54    inference(resolution,[],[f56,f25])).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    r1_tarski(sK3(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),sK0)),
% 0.21/0.54    inference(resolution,[],[f32,f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 0.21/0.54    inference(equality_resolution,[],[f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f14])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    r2_hidden(sK3(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),k1_zfmisc_1(sK0))),
% 0.21/0.54    inference(resolution,[],[f20,f26])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (7921)------------------------------
% 0.21/0.54  % (7921)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (7921)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (7921)Memory used [KB]: 1791
% 0.21/0.54  % (7921)Time elapsed: 0.116 s
% 0.21/0.54  % (7921)------------------------------
% 0.21/0.54  % (7921)------------------------------
% 0.21/0.54  % (7946)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (7920)Success in time 0.171 s
%------------------------------------------------------------------------------
