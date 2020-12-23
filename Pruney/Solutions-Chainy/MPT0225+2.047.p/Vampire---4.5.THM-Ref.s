%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:12 EST 2020

% Result     : Theorem 0.11s
% Output     : Refutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 140 expanded)
%              Number of leaves         :    8 (  44 expanded)
%              Depth                    :   12
%              Number of atoms          :  156 ( 338 expanded)
%              Number of equality atoms :  118 ( 276 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (22930)Termination reason: Refutation not found, incomplete strategy

fof(f101,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f44,f99,f36])).

% (22930)Memory used [KB]: 10618
% (22930)Time elapsed: 0.059 s
fof(f36,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X0,X0,X0,X0) != k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f22,f32,f32])).

fof(f32,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f20,f31])).

fof(f31,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f21,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

% (22930)------------------------------
% (22930)------------------------------
fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f21,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f20,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
        | r2_hidden(X0,X1) )
      & ( ~ r2_hidden(X0,X1)
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

fof(f99,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(trivial_inequality_removal,[],[f98])).

fof(f98,plain,
    ( sK0 != sK0
    | k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(backward_demodulation,[],[f48,f74])).

fof(f74,plain,(
    sK0 = sK1 ),
    inference(subsumption_resolution,[],[f73,f47])).

fof(f47,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_enumset1(X0,X0,X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f25,f31])).

fof(f25,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f16])).

fof(f16,plain,(
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

fof(f15,plain,(
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
    inference(rectify,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f73,plain,
    ( sK0 = sK1
    | r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(trivial_inequality_removal,[],[f72])).

fof(f72,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != k2_enumset1(sK0,sK0,sK0,sK0)
    | sK0 = sK1
    | r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(superposition,[],[f33,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X0,X0,X0,X0) = k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f23,f32,f32])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f33,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))
    | sK0 = sK1 ),
    inference(definition_unfolding,[],[f19,f32,f32,f32])).

fof(f19,plain,
    ( sK0 = sK1
    | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( ( sK0 = sK1
      | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) )
    & ( sK0 != sK1
      | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f10])).

fof(f10,plain,
    ( ? [X0,X1] :
        ( ( X0 = X1
          | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
        & ( X0 != X1
          | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) )
   => ( ( sK0 = sK1
        | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) )
      & ( sK0 != sK1
        | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ( X0 = X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
      & ( X0 != X1
        | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <~> X0 != X1 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
      <=> X0 != X1 ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f48,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0))
    | sK0 != sK1 ),
    inference(inner_rewriting,[],[f34])).

fof(f34,plain,
    ( sK0 != sK1
    | k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f18,f32,f32,f32])).

fof(f18,plain,
    ( sK0 != sK1
    | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f44,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_enumset1(X0,X0,X0,X4)) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f27,f31])).

fof(f27,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.06  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.07  % Command    : run_vampire %s %d
% 0.06/0.26  % Computer   : n001.cluster.edu
% 0.06/0.26  % Model      : x86_64 x86_64
% 0.06/0.26  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.06/0.26  % Memory     : 8042.1875MB
% 0.06/0.26  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.06/0.26  % CPULimit   : 60
% 0.06/0.26  % WCLimit    : 600
% 0.06/0.26  % DateTime   : Tue Dec  1 13:46:59 EST 2020
% 0.06/0.26  % CPUTime    : 
% 0.11/0.34  % (22931)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.11/0.34  % (22930)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.11/0.35  % (22929)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.11/0.35  % (22929)Refutation not found, incomplete strategy% (22929)------------------------------
% 0.11/0.35  % (22929)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.11/0.35  % (22929)Termination reason: Refutation not found, incomplete strategy
% 0.11/0.35  
% 0.11/0.35  % (22929)Memory used [KB]: 6140
% 0.11/0.35  % (22929)Time elapsed: 0.057 s
% 0.11/0.35  % (22929)------------------------------
% 0.11/0.35  % (22929)------------------------------
% 0.11/0.35  % (22930)Refutation not found, incomplete strategy% (22930)------------------------------
% 0.11/0.35  % (22930)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.11/0.35  % (22922)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.11/0.35  % (22922)Refutation found. Thanks to Tanya!
% 0.11/0.35  % SZS status Theorem for theBenchmark
% 0.11/0.35  % SZS output start Proof for theBenchmark
% 0.11/0.35  % (22930)Termination reason: Refutation not found, incomplete strategy
% 0.11/0.35  
% 0.11/0.35  fof(f101,plain,(
% 0.11/0.35    $false),
% 0.11/0.35    inference(unit_resulting_resolution,[],[f44,f99,f36])).
% 0.11/0.35  % (22930)Memory used [KB]: 10618
% 0.11/0.35  % (22930)Time elapsed: 0.059 s
% 0.11/0.35  fof(f36,plain,(
% 0.11/0.35    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X0) != k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.11/0.35    inference(definition_unfolding,[],[f22,f32,f32])).
% 0.11/0.35  fof(f32,plain,(
% 0.11/0.35    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.11/0.35    inference(definition_unfolding,[],[f20,f31])).
% 0.11/0.35  fof(f31,plain,(
% 0.11/0.35    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.11/0.35    inference(definition_unfolding,[],[f21,f24])).
% 0.11/0.35  fof(f24,plain,(
% 0.11/0.35    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.11/0.35    inference(cnf_transformation,[],[f4])).
% 0.11/0.35  % (22930)------------------------------
% 0.11/0.35  % (22930)------------------------------
% 0.11/0.35  fof(f4,axiom,(
% 0.11/0.35    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.11/0.35    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.11/0.35  fof(f21,plain,(
% 0.11/0.35    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.11/0.35    inference(cnf_transformation,[],[f3])).
% 0.11/0.35  fof(f3,axiom,(
% 0.11/0.35    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.11/0.35    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.11/0.35  fof(f20,plain,(
% 0.11/0.35    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.11/0.35    inference(cnf_transformation,[],[f2])).
% 0.11/0.35  fof(f2,axiom,(
% 0.11/0.35    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.11/0.35    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.11/0.35  fof(f22,plain,(
% 0.11/0.35    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)) )),
% 0.11/0.35    inference(cnf_transformation,[],[f12])).
% 0.11/0.35  fof(f12,plain,(
% 0.11/0.35    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) & (~r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)))),
% 0.11/0.35    inference(nnf_transformation,[],[f5])).
% 0.11/0.35  fof(f5,axiom,(
% 0.11/0.35    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 0.11/0.35    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).
% 0.11/0.35  fof(f99,plain,(
% 0.11/0.35    k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.11/0.35    inference(trivial_inequality_removal,[],[f98])).
% 0.11/0.35  fof(f98,plain,(
% 0.11/0.35    sK0 != sK0 | k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.11/0.35    inference(backward_demodulation,[],[f48,f74])).
% 0.11/0.35  fof(f74,plain,(
% 0.11/0.35    sK0 = sK1),
% 0.11/0.35    inference(subsumption_resolution,[],[f73,f47])).
% 0.11/0.35  fof(f47,plain,(
% 0.11/0.35    ( ! [X4,X0,X1] : (~r2_hidden(X4,k2_enumset1(X0,X0,X0,X1)) | X0 = X4 | X1 = X4) )),
% 0.11/0.35    inference(equality_resolution,[],[f42])).
% 0.11/0.35  fof(f42,plain,(
% 0.11/0.35    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 0.11/0.35    inference(definition_unfolding,[],[f25,f31])).
% 0.11/0.35  fof(f25,plain,(
% 0.11/0.35    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 0.11/0.35    inference(cnf_transformation,[],[f17])).
% 0.11/0.35  fof(f17,plain,(
% 0.11/0.35    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.11/0.35    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f16])).
% 0.11/0.35  fof(f16,plain,(
% 0.11/0.35    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2))))),
% 0.11/0.35    introduced(choice_axiom,[])).
% 0.11/0.35  fof(f15,plain,(
% 0.11/0.35    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.11/0.35    inference(rectify,[],[f14])).
% 0.11/0.35  fof(f14,plain,(
% 0.11/0.35    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.11/0.35    inference(flattening,[],[f13])).
% 0.11/0.35  fof(f13,plain,(
% 0.11/0.35    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.11/0.35    inference(nnf_transformation,[],[f1])).
% 0.11/0.35  fof(f1,axiom,(
% 0.11/0.35    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.11/0.35    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 0.11/0.35  fof(f73,plain,(
% 0.11/0.35    sK0 = sK1 | r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.11/0.35    inference(trivial_inequality_removal,[],[f72])).
% 0.11/0.35  fof(f72,plain,(
% 0.11/0.35    k2_enumset1(sK0,sK0,sK0,sK0) != k2_enumset1(sK0,sK0,sK0,sK0) | sK0 = sK1 | r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.11/0.35    inference(superposition,[],[f33,f35])).
% 0.11/0.35  fof(f35,plain,(
% 0.11/0.35    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X0) = k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.11/0.35    inference(definition_unfolding,[],[f23,f32,f32])).
% 0.11/0.35  fof(f23,plain,(
% 0.11/0.35    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.11/0.35    inference(cnf_transformation,[],[f12])).
% 0.11/0.35  fof(f33,plain,(
% 0.11/0.35    k2_enumset1(sK0,sK0,sK0,sK0) != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) | sK0 = sK1),
% 0.11/0.35    inference(definition_unfolding,[],[f19,f32,f32,f32])).
% 0.11/0.35  fof(f19,plain,(
% 0.11/0.35    sK0 = sK1 | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.11/0.35    inference(cnf_transformation,[],[f11])).
% 0.11/0.35  fof(f11,plain,(
% 0.11/0.35    (sK0 = sK1 | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) & (sK0 != sK1 | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 0.11/0.35    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f10])).
% 0.11/0.35  fof(f10,plain,(
% 0.11/0.35    ? [X0,X1] : ((X0 = X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) & (X0 != X1 | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))) => ((sK0 = sK1 | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) & (sK0 != sK1 | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))))),
% 0.11/0.35    introduced(choice_axiom,[])).
% 0.11/0.35  fof(f9,plain,(
% 0.11/0.35    ? [X0,X1] : ((X0 = X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) & (X0 != X1 | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 0.11/0.35    inference(nnf_transformation,[],[f8])).
% 0.11/0.35  fof(f8,plain,(
% 0.11/0.35    ? [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <~> X0 != X1)),
% 0.11/0.35    inference(ennf_transformation,[],[f7])).
% 0.11/0.35  fof(f7,negated_conjecture,(
% 0.11/0.35    ~! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.11/0.35    inference(negated_conjecture,[],[f6])).
% 0.11/0.35  fof(f6,conjecture,(
% 0.11/0.35    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.11/0.35    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.11/0.35  fof(f48,plain,(
% 0.11/0.35    k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)) | sK0 != sK1),
% 0.11/0.35    inference(inner_rewriting,[],[f34])).
% 0.11/0.35  fof(f34,plain,(
% 0.11/0.35    sK0 != sK1 | k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.11/0.35    inference(definition_unfolding,[],[f18,f32,f32,f32])).
% 0.11/0.35  fof(f18,plain,(
% 0.11/0.35    sK0 != sK1 | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.11/0.35    inference(cnf_transformation,[],[f11])).
% 0.11/0.35  fof(f44,plain,(
% 0.11/0.35    ( ! [X4,X0] : (r2_hidden(X4,k2_enumset1(X0,X0,X0,X4))) )),
% 0.11/0.35    inference(equality_resolution,[],[f43])).
% 0.11/0.35  fof(f43,plain,(
% 0.11/0.35    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X4) != X2) )),
% 0.11/0.35    inference(equality_resolution,[],[f40])).
% 0.11/0.35  fof(f40,plain,(
% 0.11/0.35    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 0.11/0.35    inference(definition_unfolding,[],[f27,f31])).
% 0.11/0.35  fof(f27,plain,(
% 0.11/0.35    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 0.11/0.35    inference(cnf_transformation,[],[f17])).
% 0.11/0.35  % SZS output end Proof for theBenchmark
% 0.11/0.35  % (22922)------------------------------
% 0.11/0.35  % (22922)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.11/0.35  % (22922)Termination reason: Refutation
% 0.11/0.35  
% 0.11/0.35  % (22922)Memory used [KB]: 1791
% 0.11/0.35  % (22922)Time elapsed: 0.058 s
% 0.11/0.35  % (22922)------------------------------
% 0.11/0.35  % (22922)------------------------------
% 0.11/0.36  % (22916)Success in time 0.09 s
%------------------------------------------------------------------------------
