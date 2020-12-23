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
% DateTime   : Thu Dec  3 12:42:12 EST 2020

% Result     : Theorem 1.55s
% Output     : Refutation 1.55s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 233 expanded)
%              Number of leaves         :    8 (  61 expanded)
%              Depth                    :   17
%              Number of atoms          :  165 ( 749 expanded)
%              Number of equality atoms :   65 ( 337 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f83,plain,(
    $false ),
    inference(resolution,[],[f79,f73])).

fof(f73,plain,(
    ~ r2_hidden(sK1,sK3) ),
    inference(resolution,[],[f72,f45])).

fof(f45,plain,(
    ! [X3] : r2_hidden(X3,k2_enumset1(X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_enumset1(X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f26,f36])).

fof(f36,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f32,f35])).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f33,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f33,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f32,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f26,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK4(X0,X1) != X0
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( sK4(X0,X1) = X0
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK4(X0,X1) != X0
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( sK4(X0,X1) = X0
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
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
    inference(rectify,[],[f16])).

fof(f16,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f72,plain,
    ( ~ r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ r2_hidden(sK1,sK3) ),
    inference(duplicate_literal_removal,[],[f69])).

fof(f69,plain,
    ( ~ r2_hidden(sK1,sK3)
    | ~ r2_hidden(sK1,sK3)
    | ~ r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(resolution,[],[f66,f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f66,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK3))
    | ~ r2_hidden(sK1,sK3) ),
    inference(trivial_inequality_removal,[],[f64])).

fof(f64,plain,
    ( sK0 != sK0
    | ~ r2_hidden(sK1,sK3)
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK3)) ),
    inference(backward_demodulation,[],[f47,f62])).

fof(f62,plain,(
    sK0 = sK2 ),
    inference(duplicate_literal_removal,[],[f56])).

fof(f56,plain,
    ( sK0 = sK2
    | sK0 = sK2 ),
    inference(resolution,[],[f51,f39])).

fof(f39,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))
    | sK0 = sK2 ),
    inference(definition_unfolding,[],[f22,f36])).

fof(f22,plain,
    ( sK0 = sK2
    | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ( ~ r2_hidden(sK1,sK3)
      | sK0 != sK2
      | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3)) )
    & ( ( r2_hidden(sK1,sK3)
        & sK0 = sK2 )
      | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ r2_hidden(X1,X3)
          | X0 != X2
          | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) )
        & ( ( r2_hidden(X1,X3)
            & X0 = X2 )
          | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) )
   => ( ( ~ r2_hidden(sK1,sK3)
        | sK0 != sK2
        | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3)) )
      & ( ( r2_hidden(sK1,sK3)
          & sK0 = sK2 )
        | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r2_hidden(X1,X3)
        | X0 != X2
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) )
      & ( ( r2_hidden(X1,X3)
          & X0 = X2 )
        | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r2_hidden(X1,X3)
        | X0 != X2
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) )
      & ( ( r2_hidden(X1,X3)
          & X0 = X2 )
        | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
    <~> ( r2_hidden(X1,X3)
        & X0 = X2 ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
      <=> ( r2_hidden(X1,X3)
          & X0 = X2 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
    <=> ( r2_hidden(X1,X3)
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_zfmisc_1)).

fof(f51,plain,(
    ! [X6,X8,X7,X5] :
      ( ~ r2_hidden(k4_tarski(X6,X7),k2_zfmisc_1(k2_enumset1(X5,X5,X5,X5),X8))
      | X5 = X6 ) ),
    inference(resolution,[],[f46,f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f46,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f25,f36])).

fof(f25,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f47,plain,
    ( sK0 != sK2
    | ~ r2_hidden(sK1,sK3)
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK3)) ),
    inference(inner_rewriting,[],[f37])).

fof(f37,plain,
    ( ~ r2_hidden(sK1,sK3)
    | sK0 != sK2
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) ),
    inference(definition_unfolding,[],[f24,f36])).

fof(f24,plain,
    ( ~ r2_hidden(sK1,sK3)
    | sK0 != sK2
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3)) ),
    inference(cnf_transformation,[],[f15])).

fof(f79,plain,(
    r2_hidden(sK1,sK3) ),
    inference(resolution,[],[f76,f65])).

fof(f65,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK3))
    | r2_hidden(sK1,sK3) ),
    inference(backward_demodulation,[],[f38,f62])).

fof(f38,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))
    | r2_hidden(sK1,sK3) ),
    inference(definition_unfolding,[],[f23,f36])).

fof(f23,plain,
    ( r2_hidden(sK1,sK3)
    | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3)) ),
    inference(cnf_transformation,[],[f15])).

fof(f76,plain,(
    ! [X0,X1] : ~ r2_hidden(k4_tarski(X0,sK1),k2_zfmisc_1(X1,sK3)) ),
    inference(resolution,[],[f73,f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:26:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 1.55/0.56  % (3852)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.55/0.57  % (3859)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.55/0.57  % (3847)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.55/0.57  % (3841)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.55/0.57  % (3868)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.55/0.57  % (3868)Refutation not found, incomplete strategy% (3868)------------------------------
% 1.55/0.57  % (3868)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.57  % (3868)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.57  
% 1.55/0.57  % (3868)Memory used [KB]: 1663
% 1.55/0.57  % (3868)Time elapsed: 0.159 s
% 1.55/0.57  % (3868)------------------------------
% 1.55/0.57  % (3868)------------------------------
% 1.55/0.57  % (3842)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.55/0.57  % (3843)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.55/0.57  % (3849)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.55/0.58  % (3842)Refutation found. Thanks to Tanya!
% 1.55/0.58  % SZS status Theorem for theBenchmark
% 1.55/0.58  % SZS output start Proof for theBenchmark
% 1.55/0.58  fof(f83,plain,(
% 1.55/0.58    $false),
% 1.55/0.58    inference(resolution,[],[f79,f73])).
% 1.55/0.58  fof(f73,plain,(
% 1.55/0.58    ~r2_hidden(sK1,sK3)),
% 1.55/0.58    inference(resolution,[],[f72,f45])).
% 1.55/0.58  fof(f45,plain,(
% 1.55/0.58    ( ! [X3] : (r2_hidden(X3,k2_enumset1(X3,X3,X3,X3))) )),
% 1.55/0.58    inference(equality_resolution,[],[f44])).
% 1.55/0.58  fof(f44,plain,(
% 1.55/0.58    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_enumset1(X3,X3,X3,X3) != X1) )),
% 1.55/0.58    inference(equality_resolution,[],[f42])).
% 1.55/0.58  fof(f42,plain,(
% 1.55/0.58    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 1.55/0.58    inference(definition_unfolding,[],[f26,f36])).
% 1.55/0.58  fof(f36,plain,(
% 1.55/0.58    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.55/0.58    inference(definition_unfolding,[],[f32,f35])).
% 1.55/0.58  fof(f35,plain,(
% 1.55/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.55/0.58    inference(definition_unfolding,[],[f33,f34])).
% 1.55/0.58  fof(f34,plain,(
% 1.55/0.58    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.55/0.58    inference(cnf_transformation,[],[f4])).
% 1.55/0.58  fof(f4,axiom,(
% 1.55/0.58    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.55/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.55/0.58  fof(f33,plain,(
% 1.55/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.55/0.58    inference(cnf_transformation,[],[f3])).
% 1.55/0.58  fof(f3,axiom,(
% 1.55/0.58    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.55/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.55/0.58  fof(f32,plain,(
% 1.55/0.58    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.55/0.58    inference(cnf_transformation,[],[f2])).
% 1.55/0.58  fof(f2,axiom,(
% 1.55/0.58    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.55/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.55/0.58  fof(f26,plain,(
% 1.55/0.58    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 1.55/0.58    inference(cnf_transformation,[],[f19])).
% 1.55/0.58  fof(f19,plain,(
% 1.55/0.58    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.55/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f18])).
% 1.55/0.58  fof(f18,plain,(
% 1.55/0.58    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1))))),
% 1.55/0.58    introduced(choice_axiom,[])).
% 1.55/0.58  fof(f17,plain,(
% 1.55/0.58    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.55/0.58    inference(rectify,[],[f16])).
% 1.55/0.58  fof(f16,plain,(
% 1.55/0.58    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.55/0.58    inference(nnf_transformation,[],[f1])).
% 1.55/0.58  fof(f1,axiom,(
% 1.55/0.58    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.55/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.55/0.58  fof(f72,plain,(
% 1.55/0.58    ~r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) | ~r2_hidden(sK1,sK3)),
% 1.55/0.58    inference(duplicate_literal_removal,[],[f69])).
% 1.55/0.58  fof(f69,plain,(
% 1.55/0.58    ~r2_hidden(sK1,sK3) | ~r2_hidden(sK1,sK3) | ~r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.55/0.58    inference(resolution,[],[f66,f31])).
% 1.55/0.58  fof(f31,plain,(
% 1.55/0.58    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 1.55/0.58    inference(cnf_transformation,[],[f21])).
% 1.55/0.58  fof(f21,plain,(
% 1.55/0.58    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 1.55/0.58    inference(flattening,[],[f20])).
% 1.55/0.58  fof(f20,plain,(
% 1.55/0.58    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 1.55/0.58    inference(nnf_transformation,[],[f8])).
% 1.55/0.58  fof(f8,axiom,(
% 1.55/0.58    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 1.55/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 1.55/0.58  fof(f66,plain,(
% 1.55/0.58    ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK3)) | ~r2_hidden(sK1,sK3)),
% 1.55/0.58    inference(trivial_inequality_removal,[],[f64])).
% 1.55/0.58  fof(f64,plain,(
% 1.55/0.58    sK0 != sK0 | ~r2_hidden(sK1,sK3) | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK3))),
% 1.55/0.58    inference(backward_demodulation,[],[f47,f62])).
% 1.55/0.58  fof(f62,plain,(
% 1.55/0.58    sK0 = sK2),
% 1.55/0.58    inference(duplicate_literal_removal,[],[f56])).
% 1.55/0.58  fof(f56,plain,(
% 1.55/0.58    sK0 = sK2 | sK0 = sK2),
% 1.55/0.58    inference(resolution,[],[f51,f39])).
% 1.55/0.58  fof(f39,plain,(
% 1.55/0.58    r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) | sK0 = sK2),
% 1.55/0.58    inference(definition_unfolding,[],[f22,f36])).
% 1.55/0.58  fof(f22,plain,(
% 1.55/0.58    sK0 = sK2 | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3))),
% 1.55/0.58    inference(cnf_transformation,[],[f15])).
% 1.55/0.58  fof(f15,plain,(
% 1.55/0.58    (~r2_hidden(sK1,sK3) | sK0 != sK2 | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3))) & ((r2_hidden(sK1,sK3) & sK0 = sK2) | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3)))),
% 1.55/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f14])).
% 1.55/0.58  fof(f14,plain,(
% 1.55/0.58    ? [X0,X1,X2,X3] : ((~r2_hidden(X1,X3) | X0 != X2 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))) & ((r2_hidden(X1,X3) & X0 = X2) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)))) => ((~r2_hidden(sK1,sK3) | sK0 != sK2 | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3))) & ((r2_hidden(sK1,sK3) & sK0 = sK2) | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3))))),
% 1.55/0.58    introduced(choice_axiom,[])).
% 1.55/0.58  fof(f13,plain,(
% 1.55/0.58    ? [X0,X1,X2,X3] : ((~r2_hidden(X1,X3) | X0 != X2 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))) & ((r2_hidden(X1,X3) & X0 = X2) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))))),
% 1.55/0.58    inference(flattening,[],[f12])).
% 1.55/0.58  fof(f12,plain,(
% 1.55/0.58    ? [X0,X1,X2,X3] : (((~r2_hidden(X1,X3) | X0 != X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))) & ((r2_hidden(X1,X3) & X0 = X2) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))))),
% 1.55/0.58    inference(nnf_transformation,[],[f11])).
% 1.55/0.58  fof(f11,plain,(
% 1.55/0.58    ? [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) <~> (r2_hidden(X1,X3) & X0 = X2))),
% 1.55/0.58    inference(ennf_transformation,[],[f10])).
% 1.55/0.58  fof(f10,negated_conjecture,(
% 1.55/0.58    ~! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) <=> (r2_hidden(X1,X3) & X0 = X2))),
% 1.55/0.58    inference(negated_conjecture,[],[f9])).
% 1.55/0.58  fof(f9,conjecture,(
% 1.55/0.58    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) <=> (r2_hidden(X1,X3) & X0 = X2))),
% 1.55/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_zfmisc_1)).
% 1.55/0.58  fof(f51,plain,(
% 1.55/0.58    ( ! [X6,X8,X7,X5] : (~r2_hidden(k4_tarski(X6,X7),k2_zfmisc_1(k2_enumset1(X5,X5,X5,X5),X8)) | X5 = X6) )),
% 1.55/0.58    inference(resolution,[],[f46,f29])).
% 1.55/0.58  fof(f29,plain,(
% 1.55/0.58    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 1.55/0.58    inference(cnf_transformation,[],[f21])).
% 1.55/0.58  fof(f46,plain,(
% 1.55/0.58    ( ! [X0,X3] : (~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) | X0 = X3) )),
% 1.55/0.58    inference(equality_resolution,[],[f43])).
% 1.55/0.58  fof(f43,plain,(
% 1.55/0.58    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 1.55/0.58    inference(definition_unfolding,[],[f25,f36])).
% 1.55/0.58  fof(f25,plain,(
% 1.55/0.58    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.55/0.58    inference(cnf_transformation,[],[f19])).
% 1.55/0.58  fof(f47,plain,(
% 1.55/0.58    sK0 != sK2 | ~r2_hidden(sK1,sK3) | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK3))),
% 1.55/0.58    inference(inner_rewriting,[],[f37])).
% 1.55/0.58  fof(f37,plain,(
% 1.55/0.58    ~r2_hidden(sK1,sK3) | sK0 != sK2 | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))),
% 1.55/0.58    inference(definition_unfolding,[],[f24,f36])).
% 1.55/0.58  fof(f24,plain,(
% 1.55/0.58    ~r2_hidden(sK1,sK3) | sK0 != sK2 | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3))),
% 1.55/0.58    inference(cnf_transformation,[],[f15])).
% 1.55/0.58  fof(f79,plain,(
% 1.55/0.58    r2_hidden(sK1,sK3)),
% 1.55/0.58    inference(resolution,[],[f76,f65])).
% 1.55/0.58  fof(f65,plain,(
% 1.55/0.58    r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK3)) | r2_hidden(sK1,sK3)),
% 1.55/0.58    inference(backward_demodulation,[],[f38,f62])).
% 1.55/0.58  fof(f38,plain,(
% 1.55/0.58    r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) | r2_hidden(sK1,sK3)),
% 1.55/0.58    inference(definition_unfolding,[],[f23,f36])).
% 1.55/0.58  fof(f23,plain,(
% 1.55/0.58    r2_hidden(sK1,sK3) | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3))),
% 1.55/0.58    inference(cnf_transformation,[],[f15])).
% 1.55/0.58  fof(f76,plain,(
% 1.55/0.58    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,sK1),k2_zfmisc_1(X1,sK3))) )),
% 1.55/0.58    inference(resolution,[],[f73,f30])).
% 1.55/0.58  fof(f30,plain,(
% 1.55/0.58    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 1.55/0.58    inference(cnf_transformation,[],[f21])).
% 1.55/0.58  % SZS output end Proof for theBenchmark
% 1.55/0.58  % (3842)------------------------------
% 1.55/0.58  % (3842)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.58  % (3842)Termination reason: Refutation
% 1.55/0.58  
% 1.55/0.58  % (3842)Memory used [KB]: 1791
% 1.55/0.58  % (3842)Time elapsed: 0.150 s
% 1.55/0.58  % (3842)------------------------------
% 1.55/0.58  % (3842)------------------------------
% 1.55/0.58  % (3830)Success in time 0.223 s
%------------------------------------------------------------------------------
