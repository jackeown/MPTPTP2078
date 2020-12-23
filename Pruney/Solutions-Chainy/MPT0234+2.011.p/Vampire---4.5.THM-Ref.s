%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:26 EST 2020

% Result     : Theorem 1.19s
% Output     : Refutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :   27 (  32 expanded)
%              Number of leaves         :    7 (   9 expanded)
%              Depth                    :    8
%              Number of atoms          :   81 (  93 expanded)
%              Number of equality atoms :   53 (  65 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f47,plain,(
    $false ),
    inference(subsumption_resolution,[],[f46,f19])).

fof(f19,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f13])).

% (30955)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% (30955)Refutation not found, incomplete strategy% (30955)------------------------------
% (30955)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (30955)Termination reason: Refutation not found, incomplete strategy

% (30955)Memory used [KB]: 10618
% (30955)Time elapsed: 0.107 s
% (30955)------------------------------
% (30955)------------------------------
% (30959)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% (30959)Refutation not found, incomplete strategy% (30959)------------------------------
% (30959)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (30959)Termination reason: Refutation not found, incomplete strategy

% (30959)Memory used [KB]: 10618
% (30959)Time elapsed: 0.115 s
% (30959)------------------------------
% (30959)------------------------------
% (30957)Refutation not found, incomplete strategy% (30957)------------------------------
% (30957)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (30957)Termination reason: Refutation not found, incomplete strategy

% (30957)Memory used [KB]: 1663
% (30957)Time elapsed: 0.116 s
% (30957)------------------------------
% (30957)------------------------------
% (30949)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% (30958)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% (30954)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% (30951)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% (30961)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% (30961)Refutation not found, incomplete strategy% (30961)------------------------------
% (30961)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (30961)Termination reason: Refutation not found, incomplete strategy

% (30961)Memory used [KB]: 1663
% (30961)Time elapsed: 0.128 s
% (30961)------------------------------
% (30961)------------------------------
% (30948)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% (30953)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% (30946)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
fof(f13,plain,
    ( k2_tarski(sK0,sK1) != k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    & sK0 != sK1 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f12])).

fof(f12,plain,
    ( ? [X0,X1] :
        ( k2_tarski(X0,X1) != k5_xboole_0(k1_tarski(X0),k1_tarski(X1))
        & X0 != X1 )
   => ( k2_tarski(sK0,sK1) != k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
      & sK0 != sK1 ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] :
      ( k2_tarski(X0,X1) != k5_xboole_0(k1_tarski(X0),k1_tarski(X1))
      & X0 != X1 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( X0 != X1
       => k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( X0 != X1
     => k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_zfmisc_1)).

fof(f46,plain,(
    sK0 = sK1 ),
    inference(resolution,[],[f43,f35])).

fof(f35,plain,(
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

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f16])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
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

fof(f43,plain,(
    r2_hidden(sK1,k1_tarski(sK0)) ),
    inference(trivial_inequality_removal,[],[f42])).

fof(f42,plain,
    ( k2_tarski(sK0,sK1) != k2_tarski(sK0,sK1)
    | r2_hidden(sK1,k1_tarski(sK0)) ),
    inference(superposition,[],[f20,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | r2_hidden(X1,k1_tarski(X0)) ) ),
    inference(superposition,[],[f38,f25])).

fof(f25,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f38,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,k1_tarski(X2)) = k5_xboole_0(X3,k1_tarski(X2))
      | r2_hidden(X2,X3) ) ),
    inference(superposition,[],[f23,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
        | r2_hidden(X0,X1) )
      & ( ~ r2_hidden(X0,X1)
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f20,plain,(
    k2_tarski(sK0,sK1) != k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:11:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.51  % (30965)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.51  % (30945)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.19/0.51  % (30957)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.19/0.52  % (30952)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.19/0.52  % (30952)Refutation found. Thanks to Tanya!
% 1.19/0.52  % SZS status Theorem for theBenchmark
% 1.19/0.52  % SZS output start Proof for theBenchmark
% 1.19/0.52  fof(f47,plain,(
% 1.19/0.52    $false),
% 1.19/0.52    inference(subsumption_resolution,[],[f46,f19])).
% 1.19/0.52  fof(f19,plain,(
% 1.19/0.52    sK0 != sK1),
% 1.19/0.52    inference(cnf_transformation,[],[f13])).
% 1.19/0.52  % (30955)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.19/0.52  % (30955)Refutation not found, incomplete strategy% (30955)------------------------------
% 1.19/0.52  % (30955)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.19/0.52  % (30955)Termination reason: Refutation not found, incomplete strategy
% 1.19/0.52  
% 1.19/0.52  % (30955)Memory used [KB]: 10618
% 1.19/0.52  % (30955)Time elapsed: 0.107 s
% 1.19/0.52  % (30955)------------------------------
% 1.19/0.52  % (30955)------------------------------
% 1.19/0.52  % (30959)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.19/0.53  % (30959)Refutation not found, incomplete strategy% (30959)------------------------------
% 1.19/0.53  % (30959)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.19/0.53  % (30959)Termination reason: Refutation not found, incomplete strategy
% 1.19/0.53  
% 1.19/0.53  % (30959)Memory used [KB]: 10618
% 1.19/0.53  % (30959)Time elapsed: 0.115 s
% 1.19/0.53  % (30959)------------------------------
% 1.19/0.53  % (30959)------------------------------
% 1.19/0.53  % (30957)Refutation not found, incomplete strategy% (30957)------------------------------
% 1.19/0.53  % (30957)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.19/0.53  % (30957)Termination reason: Refutation not found, incomplete strategy
% 1.19/0.53  
% 1.19/0.53  % (30957)Memory used [KB]: 1663
% 1.19/0.53  % (30957)Time elapsed: 0.116 s
% 1.19/0.53  % (30957)------------------------------
% 1.19/0.53  % (30957)------------------------------
% 1.19/0.53  % (30949)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.37/0.53  % (30958)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.37/0.53  % (30954)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.37/0.53  % (30951)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.37/0.53  % (30961)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.37/0.53  % (30961)Refutation not found, incomplete strategy% (30961)------------------------------
% 1.37/0.53  % (30961)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.53  % (30961)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.53  
% 1.37/0.53  % (30961)Memory used [KB]: 1663
% 1.37/0.53  % (30961)Time elapsed: 0.128 s
% 1.37/0.53  % (30961)------------------------------
% 1.37/0.53  % (30961)------------------------------
% 1.37/0.54  % (30948)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.37/0.54  % (30953)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.37/0.54  % (30946)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.37/0.54  fof(f13,plain,(
% 1.37/0.54    k2_tarski(sK0,sK1) != k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) & sK0 != sK1),
% 1.37/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f12])).
% 1.37/0.54  fof(f12,plain,(
% 1.37/0.54    ? [X0,X1] : (k2_tarski(X0,X1) != k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) & X0 != X1) => (k2_tarski(sK0,sK1) != k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) & sK0 != sK1)),
% 1.37/0.54    introduced(choice_axiom,[])).
% 1.37/0.54  fof(f11,plain,(
% 1.37/0.54    ? [X0,X1] : (k2_tarski(X0,X1) != k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) & X0 != X1)),
% 1.37/0.54    inference(ennf_transformation,[],[f10])).
% 1.37/0.54  fof(f10,negated_conjecture,(
% 1.37/0.54    ~! [X0,X1] : (X0 != X1 => k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 1.37/0.54    inference(negated_conjecture,[],[f9])).
% 1.37/0.54  fof(f9,conjecture,(
% 1.37/0.54    ! [X0,X1] : (X0 != X1 => k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_zfmisc_1)).
% 1.37/0.54  fof(f46,plain,(
% 1.37/0.54    sK0 = sK1),
% 1.37/0.54    inference(resolution,[],[f43,f35])).
% 1.37/0.54  fof(f35,plain,(
% 1.37/0.54    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 1.37/0.54    inference(equality_resolution,[],[f26])).
% 1.37/0.54  fof(f26,plain,(
% 1.37/0.54    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.37/0.54    inference(cnf_transformation,[],[f17])).
% 1.37/0.54  fof(f17,plain,(
% 1.37/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.37/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f16])).
% 1.37/0.54  fof(f16,plain,(
% 1.37/0.54    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 1.37/0.54    introduced(choice_axiom,[])).
% 1.37/0.54  fof(f15,plain,(
% 1.37/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.37/0.54    inference(rectify,[],[f14])).
% 1.37/0.54  fof(f14,plain,(
% 1.37/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.37/0.54    inference(nnf_transformation,[],[f3])).
% 1.37/0.54  fof(f3,axiom,(
% 1.37/0.54    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.37/0.54  fof(f43,plain,(
% 1.37/0.54    r2_hidden(sK1,k1_tarski(sK0))),
% 1.37/0.54    inference(trivial_inequality_removal,[],[f42])).
% 1.37/0.54  fof(f42,plain,(
% 1.37/0.54    k2_tarski(sK0,sK1) != k2_tarski(sK0,sK1) | r2_hidden(sK1,k1_tarski(sK0))),
% 1.37/0.54    inference(superposition,[],[f20,f39])).
% 1.37/0.54  fof(f39,plain,(
% 1.37/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) | r2_hidden(X1,k1_tarski(X0))) )),
% 1.37/0.54    inference(superposition,[],[f38,f25])).
% 1.37/0.54  fof(f25,plain,(
% 1.37/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.37/0.54    inference(cnf_transformation,[],[f4])).
% 1.37/0.54  fof(f4,axiom,(
% 1.37/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).
% 1.37/0.54  fof(f38,plain,(
% 1.37/0.54    ( ! [X2,X3] : (k2_xboole_0(X3,k1_tarski(X2)) = k5_xboole_0(X3,k1_tarski(X2)) | r2_hidden(X2,X3)) )),
% 1.37/0.54    inference(superposition,[],[f23,f31])).
% 1.37/0.54  fof(f31,plain,(
% 1.37/0.54    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f18])).
% 1.37/0.54  fof(f18,plain,(
% 1.37/0.54    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) & (~r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)))),
% 1.37/0.54    inference(nnf_transformation,[],[f8])).
% 1.37/0.54  fof(f8,axiom,(
% 1.37/0.54    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).
% 1.37/0.54  fof(f23,plain,(
% 1.37/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.37/0.54    inference(cnf_transformation,[],[f2])).
% 1.37/0.54  fof(f2,axiom,(
% 1.37/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.37/0.54  fof(f20,plain,(
% 1.37/0.54    k2_tarski(sK0,sK1) != k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.37/0.54    inference(cnf_transformation,[],[f13])).
% 1.37/0.54  % SZS output end Proof for theBenchmark
% 1.37/0.54  % (30952)------------------------------
% 1.37/0.54  % (30952)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.54  % (30952)Termination reason: Refutation
% 1.37/0.54  
% 1.37/0.54  % (30952)Memory used [KB]: 1663
% 1.37/0.54  % (30952)Time elapsed: 0.104 s
% 1.37/0.54  % (30952)------------------------------
% 1.37/0.54  % (30952)------------------------------
% 1.37/0.54  % (30942)Success in time 0.179 s
%------------------------------------------------------------------------------
