%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:29 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   51 (  89 expanded)
%              Number of leaves         :   12 (  31 expanded)
%              Depth                    :   11
%              Number of atoms          :  177 ( 295 expanded)
%              Number of equality atoms :  103 ( 191 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f82,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f60,f71,f77,f81])).

fof(f81,plain,
    ( spl3_1
    | ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f78])).

fof(f78,plain,
    ( $false
    | spl3_1
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f54,f54,f66,f49])).

fof(f49,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k1_enumset1(X0,X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f40])).

% (24995)Refutation not found, incomplete strategy% (24995)------------------------------
% (24995)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f23,f21])).

fof(f21,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f23,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK2(X0,X1,X2) != X1
              & sK2(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( sK2(X0,X1,X2) = X1
            | sK2(X0,X1,X2) = X0
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f13,f14])).

% (24995)Termination reason: Refutation not found, incomplete strategy

% (24995)Memory used [KB]: 1663
% (24995)Time elapsed: 0.113 s
% (24995)------------------------------
% (24995)------------------------------
% (24983)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f14,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK2(X0,X1,X2) != X1
            & sK2(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( sK2(X0,X1,X2) = X1
          | sK2(X0,X1,X2) = X0
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

% (24977)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

% (24998)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f66,plain,
    ( r2_hidden(sK0,k1_enumset1(sK1,sK1,sK1))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl3_3
  <=> r2_hidden(sK0,k1_enumset1(sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f54,plain,
    ( sK0 != sK1
    | spl3_1 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl3_1
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f77,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f72])).

fof(f72,plain,
    ( $false
    | spl3_4 ),
    inference(unit_resulting_resolution,[],[f46,f70])).

fof(f70,plain,
    ( ~ r2_hidden(sK1,k1_enumset1(sK1,sK1,sK1))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl3_4
  <=> r2_hidden(sK1,k1_enumset1(sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f46,plain,(
    ! [X4,X0] : r2_hidden(X4,k1_enumset1(X0,X0,X4)) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k1_enumset1(X0,X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f25,f21])).

fof(f25,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f71,plain,
    ( spl3_3
    | ~ spl3_4
    | spl3_2 ),
    inference(avatar_split_clause,[],[f62,f57,f68,f64])).

fof(f57,plain,
    ( spl3_2
  <=> k1_enumset1(sK0,sK0,sK0) = k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK1,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f62,plain,
    ( ~ r2_hidden(sK1,k1_enumset1(sK1,sK1,sK1))
    | r2_hidden(sK0,k1_enumset1(sK1,sK1,sK1))
    | spl3_2 ),
    inference(trivial_inequality_removal,[],[f61])).

fof(f61,plain,
    ( k1_enumset1(sK0,sK0,sK0) != k1_enumset1(sK0,sK0,sK0)
    | ~ r2_hidden(sK1,k1_enumset1(sK1,sK1,sK1))
    | r2_hidden(sK0,k1_enumset1(sK1,sK1,sK1))
    | spl3_2 ),
    inference(superposition,[],[f59,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k1_enumset1(X0,X0,X0) = k5_xboole_0(k1_enumset1(X0,X0,X1),k3_xboole_0(k1_enumset1(X0,X0,X1),X2))
      | ~ r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f31,f33,f22,f21])).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f33,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f20,f21])).

fof(f20,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l38_zfmisc_1)).

fof(f59,plain,
    ( k1_enumset1(sK0,sK0,sK0) != k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK1,sK1,sK1)))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f60,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f34,f57])).

fof(f34,plain,(
    k1_enumset1(sK0,sK0,sK0) != k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f19,f33,f22,f21,f33])).

fof(f19,plain,(
    k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK1))
    & sK0 != sK1 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f9])).

fof(f9,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1))
        & X0 != X1 )
   => ( k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK1))
      & sK0 != sK1 ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1))
      & X0 != X1 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( X0 != X1
       => k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( X0 != X1
     => k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_zfmisc_1)).

fof(f55,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f18,f52])).

fof(f18,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n013.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:09:24 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.53  % (24978)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (24987)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.53  % (25003)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (24995)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.54  % (24987)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % (25003)Refutation not found, incomplete strategy% (25003)------------------------------
% 0.21/0.54  % (25003)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (24979)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (25003)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (25003)Memory used [KB]: 6140
% 0.21/0.54  % (25003)Time elapsed: 0.113 s
% 0.21/0.54  % (25003)------------------------------
% 0.21/0.54  % (25003)------------------------------
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f82,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f55,f60,f71,f77,f81])).
% 0.21/0.54  fof(f81,plain,(
% 0.21/0.54    spl3_1 | ~spl3_3),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f78])).
% 0.21/0.54  fof(f78,plain,(
% 0.21/0.54    $false | (spl3_1 | ~spl3_3)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f54,f54,f66,f49])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    ( ! [X4,X0,X1] : (~r2_hidden(X4,k1_enumset1(X0,X0,X1)) | X0 = X4 | X1 = X4) )),
% 0.21/0.54    inference(equality_resolution,[],[f40])).
% 0.21/0.54  % (24995)Refutation not found, incomplete strategy% (24995)------------------------------
% 0.21/0.54  % (24995)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k1_enumset1(X0,X0,X1) != X2) )),
% 0.21/0.54    inference(definition_unfolding,[],[f23,f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f13,f14])).
% 0.21/0.54  % (24995)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (24995)Memory used [KB]: 1663
% 0.21/0.54  % (24995)Time elapsed: 0.113 s
% 0.21/0.54  % (24995)------------------------------
% 0.21/0.54  % (24995)------------------------------
% 0.21/0.54  % (24983)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  % (24977)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  fof(f13,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.21/0.54    inference(rectify,[],[f12])).
% 0.21/0.54  fof(f12,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.21/0.54    inference(flattening,[],[f11])).
% 0.21/0.54  fof(f11,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.21/0.54    inference(nnf_transformation,[],[f2])).
% 0.21/0.54  % (24998)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 0.21/0.54  fof(f66,plain,(
% 0.21/0.54    r2_hidden(sK0,k1_enumset1(sK1,sK1,sK1)) | ~spl3_3),
% 0.21/0.54    inference(avatar_component_clause,[],[f64])).
% 0.21/0.54  fof(f64,plain,(
% 0.21/0.54    spl3_3 <=> r2_hidden(sK0,k1_enumset1(sK1,sK1,sK1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    sK0 != sK1 | spl3_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f52])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    spl3_1 <=> sK0 = sK1),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.54  fof(f77,plain,(
% 0.21/0.54    spl3_4),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f72])).
% 0.21/0.54  fof(f72,plain,(
% 0.21/0.54    $false | spl3_4),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f46,f70])).
% 0.21/0.54  fof(f70,plain,(
% 0.21/0.54    ~r2_hidden(sK1,k1_enumset1(sK1,sK1,sK1)) | spl3_4),
% 0.21/0.54    inference(avatar_component_clause,[],[f68])).
% 0.21/0.54  fof(f68,plain,(
% 0.21/0.54    spl3_4 <=> r2_hidden(sK1,k1_enumset1(sK1,sK1,sK1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    ( ! [X4,X0] : (r2_hidden(X4,k1_enumset1(X0,X0,X4))) )),
% 0.21/0.54    inference(equality_resolution,[],[f45])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k1_enumset1(X0,X0,X4) != X2) )),
% 0.21/0.54    inference(equality_resolution,[],[f38])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k1_enumset1(X0,X0,X1) != X2) )),
% 0.21/0.54    inference(definition_unfolding,[],[f25,f21])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f71,plain,(
% 0.21/0.54    spl3_3 | ~spl3_4 | spl3_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f62,f57,f68,f64])).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    spl3_2 <=> k1_enumset1(sK0,sK0,sK0) = k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK1,sK1,sK1)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.54  fof(f62,plain,(
% 0.21/0.54    ~r2_hidden(sK1,k1_enumset1(sK1,sK1,sK1)) | r2_hidden(sK0,k1_enumset1(sK1,sK1,sK1)) | spl3_2),
% 0.21/0.54    inference(trivial_inequality_removal,[],[f61])).
% 0.21/0.54  fof(f61,plain,(
% 0.21/0.54    k1_enumset1(sK0,sK0,sK0) != k1_enumset1(sK0,sK0,sK0) | ~r2_hidden(sK1,k1_enumset1(sK1,sK1,sK1)) | r2_hidden(sK0,k1_enumset1(sK1,sK1,sK1)) | spl3_2),
% 0.21/0.54    inference(superposition,[],[f59,f42])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X0,X0) = k5_xboole_0(k1_enumset1(X0,X0,X1),k3_xboole_0(k1_enumset1(X0,X0,X1),X2)) | ~r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f31,f33,f22,f21])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f20,f21])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) | (X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2)) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 0.21/0.54    inference(flattening,[],[f16])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) | ((X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2))) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 0.21/0.54    inference(nnf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l38_zfmisc_1)).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    k1_enumset1(sK0,sK0,sK0) != k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK1,sK1,sK1))) | spl3_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f57])).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    ~spl3_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f34,f57])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    k1_enumset1(sK0,sK0,sK0) != k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK1,sK1,sK1)))),
% 0.21/0.54    inference(definition_unfolding,[],[f19,f33,f22,f21,f33])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK1))),
% 0.21/0.54    inference(cnf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,plain,(
% 0.21/0.54    k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK1)) & sK0 != sK1),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f9])).
% 0.21/0.54  fof(f9,plain,(
% 0.21/0.54    ? [X0,X1] : (k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) & X0 != X1) => (k1_tarski(sK0) != k4_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK1)) & sK0 != sK1)),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f8,plain,(
% 0.21/0.54    ? [X0,X1] : (k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) & X0 != X1)),
% 0.21/0.54    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1] : (X0 != X1 => k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)))),
% 0.21/0.54    inference(negated_conjecture,[],[f6])).
% 0.21/0.54  fof(f6,conjecture,(
% 0.21/0.54    ! [X0,X1] : (X0 != X1 => k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_zfmisc_1)).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    ~spl3_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f18,f52])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    sK0 != sK1),
% 0.21/0.54    inference(cnf_transformation,[],[f10])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (24987)------------------------------
% 0.21/0.54  % (24987)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (24987)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (24987)Memory used [KB]: 10746
% 0.21/0.54  % (24987)Time elapsed: 0.117 s
% 0.21/0.54  % (24987)------------------------------
% 0.21/0.54  % (24987)------------------------------
% 0.21/0.55  % (24976)Success in time 0.176 s
%------------------------------------------------------------------------------
