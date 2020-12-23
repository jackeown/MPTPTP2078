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
% DateTime   : Thu Dec  3 12:34:54 EST 2020

% Result     : Theorem 1.38s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 151 expanded)
%              Number of leaves         :   12 (  44 expanded)
%              Depth                    :   15
%              Number of atoms          :  176 ( 411 expanded)
%              Number of equality atoms :   89 ( 233 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f140,plain,(
    $false ),
    inference(subsumption_resolution,[],[f139,f55])).

fof(f55,plain,(
    r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f42,f53])).

fof(f53,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(resolution,[],[f42,f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f25,f27])).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

% (15617)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f25,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f139,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f135,f47])).

fof(f47,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).

% (15619)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
fof(f16,plain,(
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

fof(f15,plain,(
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
    inference(rectify,[],[f14])).

fof(f14,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f135,plain,(
    ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f134,f41])).

fof(f41,plain,(
    k1_zfmisc_1(k1_xboole_0) != k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f22,f40])).

fof(f40,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f23,f39])).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f26,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f36,f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f36,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f26,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f23,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f22,plain,(
    k1_zfmisc_1(k1_xboole_0) != k1_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    k1_zfmisc_1(k1_xboole_0) != k1_tarski(k1_xboole_0) ),
    inference(flattening,[],[f11])).

fof(f11,negated_conjecture,(
    k1_zfmisc_1(k1_xboole_0) != k1_tarski(k1_xboole_0) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).

fof(f134,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f130,f50])).

fof(f50,plain,(
    ! [X3] : r2_hidden(X3,k3_enumset1(X3,X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k3_enumset1(X3,X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f33,f40])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f20])).

fof(f20,plain,(
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

fof(f19,plain,(
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
    inference(rectify,[],[f18])).

fof(f18,plain,(
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
    inference(nnf_transformation,[],[f4])).

% (15609)Termination reason: Refutation not found, incomplete strategy

% (15609)Memory used [KB]: 1663
fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

% (15609)Time elapsed: 0.130 s
% (15609)------------------------------
% (15609)------------------------------
% (15619)Refutation not found, incomplete strategy% (15619)------------------------------
% (15619)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f130,plain,
    ( ~ r2_hidden(k1_xboole_0,k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | k1_zfmisc_1(k1_xboole_0) = k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f67,f95])).

% (15611)Refutation not found, incomplete strategy% (15611)------------------------------
% (15611)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (15611)Termination reason: Refutation not found, incomplete strategy

% (15611)Memory used [KB]: 10618
% (15611)Time elapsed: 0.135 s
% (15611)------------------------------
% (15611)------------------------------
fof(f95,plain,(
    k1_xboole_0 = sK1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(trivial_inequality_removal,[],[f94])).

fof(f94,plain,
    ( k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)
    | k1_xboole_0 = sK1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(duplicate_literal_removal,[],[f89])).

fof(f89,plain,
    ( k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0)
    | k1_xboole_0 = sK1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f41,f87])).

fof(f87,plain,(
    ! [X0] :
      ( k1_zfmisc_1(k1_xboole_0) = k3_enumset1(X0,X0,X0,X0,X0)
      | sK1(X0,k1_zfmisc_1(k1_xboole_0)) = X0
      | k1_xboole_0 = sK1(X0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(resolution,[],[f68,f24])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(sK1(X0,k1_zfmisc_1(X1)),X1)
      | k3_enumset1(X0,X0,X0,X0,X0) = k1_zfmisc_1(X1)
      | sK1(X0,k1_zfmisc_1(X1)) = X0 ) ),
    inference(resolution,[],[f44,f48])).

fof(f48,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | sK1(X0,X1) = X0
      | k3_enumset1(X0,X0,X0,X0,X0) = X1 ) ),
    inference(definition_unfolding,[],[f34,f40])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK1(X0,X1) = X0
      | r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f67,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(sK1(X2,X3),k3_enumset1(X2,X2,X2,X2,X2))
      | k3_enumset1(X2,X2,X2,X2,X2) = X3
      | ~ r2_hidden(X2,X3) ) ),
    inference(extensionality_resolution,[],[f51,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( sK1(X0,X1) != X0
      | k3_enumset1(X0,X0,X0,X0,X0) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(inner_rewriting,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k3_enumset1(X0,X0,X0,X0,X0) = X1
      | sK1(X0,X1) != X0
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f35,f40])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK1(X0,X1) != X0
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f51,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f32,f40])).

fof(f32,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:57:09 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.38/0.56  % (15603)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.38/0.56  % (15601)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.38/0.56  % (15602)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.38/0.57  % (15601)Refutation found. Thanks to Tanya!
% 1.38/0.57  % SZS status Theorem for theBenchmark
% 1.38/0.57  % (15609)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.38/0.57  % (15611)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.38/0.57  % (15609)Refutation not found, incomplete strategy% (15609)------------------------------
% 1.38/0.57  % (15609)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.57  % SZS output start Proof for theBenchmark
% 1.38/0.57  fof(f140,plain,(
% 1.38/0.57    $false),
% 1.38/0.57    inference(subsumption_resolution,[],[f139,f55])).
% 1.38/0.57  fof(f55,plain,(
% 1.38/0.57    r1_tarski(k1_xboole_0,k1_xboole_0)),
% 1.38/0.57    inference(superposition,[],[f42,f53])).
% 1.38/0.57  fof(f53,plain,(
% 1.38/0.57    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) )),
% 1.38/0.57    inference(resolution,[],[f42,f24])).
% 1.38/0.57  fof(f24,plain,(
% 1.38/0.57    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.38/0.57    inference(cnf_transformation,[],[f13])).
% 1.38/0.57  fof(f13,plain,(
% 1.38/0.57    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 1.38/0.57    inference(ennf_transformation,[],[f3])).
% 1.38/0.57  fof(f3,axiom,(
% 1.38/0.57    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 1.38/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 1.38/0.57  fof(f42,plain,(
% 1.38/0.57    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 1.38/0.57    inference(definition_unfolding,[],[f25,f27])).
% 1.38/0.57  fof(f27,plain,(
% 1.38/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.38/0.57    inference(cnf_transformation,[],[f1])).
% 1.38/0.57  % (15617)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.38/0.57  fof(f1,axiom,(
% 1.38/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.38/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.38/0.57  fof(f25,plain,(
% 1.38/0.57    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.38/0.57    inference(cnf_transformation,[],[f2])).
% 1.38/0.57  fof(f2,axiom,(
% 1.38/0.57    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.38/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.38/0.57  fof(f139,plain,(
% 1.38/0.57    ~r1_tarski(k1_xboole_0,k1_xboole_0)),
% 1.38/0.57    inference(resolution,[],[f135,f47])).
% 1.38/0.57  fof(f47,plain,(
% 1.38/0.57    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 1.38/0.57    inference(equality_resolution,[],[f29])).
% 1.38/0.57  fof(f29,plain,(
% 1.38/0.57    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 1.38/0.57    inference(cnf_transformation,[],[f17])).
% 1.38/0.57  fof(f17,plain,(
% 1.38/0.57    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.38/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).
% 1.38/0.57  % (15619)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.38/0.57  fof(f16,plain,(
% 1.38/0.57    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 1.38/0.57    introduced(choice_axiom,[])).
% 1.38/0.57  fof(f15,plain,(
% 1.38/0.57    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.38/0.57    inference(rectify,[],[f14])).
% 1.38/0.57  fof(f14,plain,(
% 1.38/0.57    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.38/0.57    inference(nnf_transformation,[],[f9])).
% 1.38/0.57  fof(f9,axiom,(
% 1.38/0.57    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.38/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.38/0.57  fof(f135,plain,(
% 1.38/0.57    ~r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 1.38/0.57    inference(subsumption_resolution,[],[f134,f41])).
% 1.38/0.57  fof(f41,plain,(
% 1.38/0.57    k1_zfmisc_1(k1_xboole_0) != k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 1.38/0.57    inference(definition_unfolding,[],[f22,f40])).
% 1.38/0.57  fof(f40,plain,(
% 1.38/0.57    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.38/0.57    inference(definition_unfolding,[],[f23,f39])).
% 1.38/0.57  fof(f39,plain,(
% 1.38/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.38/0.57    inference(definition_unfolding,[],[f26,f38])).
% 1.38/0.57  fof(f38,plain,(
% 1.38/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.38/0.57    inference(definition_unfolding,[],[f36,f37])).
% 1.38/0.57  fof(f37,plain,(
% 1.38/0.57    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.38/0.57    inference(cnf_transformation,[],[f8])).
% 1.38/0.57  fof(f8,axiom,(
% 1.38/0.57    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.38/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.38/0.57  fof(f36,plain,(
% 1.38/0.57    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.38/0.57    inference(cnf_transformation,[],[f7])).
% 1.38/0.57  fof(f7,axiom,(
% 1.38/0.57    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.38/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.38/0.57  fof(f26,plain,(
% 1.38/0.57    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.38/0.57    inference(cnf_transformation,[],[f6])).
% 1.38/0.57  fof(f6,axiom,(
% 1.38/0.57    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.38/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.38/0.57  fof(f23,plain,(
% 1.38/0.57    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.38/0.57    inference(cnf_transformation,[],[f5])).
% 1.38/0.57  fof(f5,axiom,(
% 1.38/0.57    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.38/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.38/0.57  fof(f22,plain,(
% 1.38/0.57    k1_zfmisc_1(k1_xboole_0) != k1_tarski(k1_xboole_0)),
% 1.38/0.57    inference(cnf_transformation,[],[f12])).
% 1.38/0.57  fof(f12,plain,(
% 1.38/0.57    k1_zfmisc_1(k1_xboole_0) != k1_tarski(k1_xboole_0)),
% 1.38/0.57    inference(flattening,[],[f11])).
% 1.38/0.57  fof(f11,negated_conjecture,(
% 1.38/0.57    ~k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 1.38/0.57    inference(negated_conjecture,[],[f10])).
% 1.38/0.57  fof(f10,conjecture,(
% 1.38/0.57    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 1.38/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).
% 1.38/0.57  fof(f134,plain,(
% 1.38/0.57    k1_zfmisc_1(k1_xboole_0) = k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 1.38/0.57    inference(subsumption_resolution,[],[f130,f50])).
% 1.38/0.57  fof(f50,plain,(
% 1.38/0.57    ( ! [X3] : (r2_hidden(X3,k3_enumset1(X3,X3,X3,X3,X3))) )),
% 1.38/0.57    inference(equality_resolution,[],[f49])).
% 1.38/0.57  fof(f49,plain,(
% 1.38/0.57    ( ! [X3,X1] : (r2_hidden(X3,X1) | k3_enumset1(X3,X3,X3,X3,X3) != X1) )),
% 1.38/0.57    inference(equality_resolution,[],[f45])).
% 1.38/0.57  fof(f45,plain,(
% 1.38/0.57    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 1.38/0.57    inference(definition_unfolding,[],[f33,f40])).
% 1.38/0.57  fof(f33,plain,(
% 1.38/0.57    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 1.38/0.57    inference(cnf_transformation,[],[f21])).
% 1.38/0.57  fof(f21,plain,(
% 1.38/0.57    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.38/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f20])).
% 1.38/0.57  fof(f20,plain,(
% 1.38/0.57    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 1.38/0.57    introduced(choice_axiom,[])).
% 1.38/0.57  fof(f19,plain,(
% 1.38/0.57    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.38/0.57    inference(rectify,[],[f18])).
% 1.38/0.57  fof(f18,plain,(
% 1.38/0.57    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.38/0.57    inference(nnf_transformation,[],[f4])).
% 1.38/0.57  % (15609)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.57  
% 1.38/0.57  % (15609)Memory used [KB]: 1663
% 1.38/0.57  fof(f4,axiom,(
% 1.38/0.57    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.38/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.38/0.57  % (15609)Time elapsed: 0.130 s
% 1.38/0.57  % (15609)------------------------------
% 1.38/0.57  % (15609)------------------------------
% 1.38/0.57  % (15619)Refutation not found, incomplete strategy% (15619)------------------------------
% 1.38/0.57  % (15619)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.58  fof(f130,plain,(
% 1.38/0.58    ~r2_hidden(k1_xboole_0,k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) | k1_zfmisc_1(k1_xboole_0) = k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 1.38/0.58    inference(superposition,[],[f67,f95])).
% 1.38/0.58  % (15611)Refutation not found, incomplete strategy% (15611)------------------------------
% 1.38/0.58  % (15611)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.58  % (15611)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.58  
% 1.38/0.58  % (15611)Memory used [KB]: 10618
% 1.38/0.58  % (15611)Time elapsed: 0.135 s
% 1.38/0.58  % (15611)------------------------------
% 1.38/0.58  % (15611)------------------------------
% 1.38/0.58  fof(f95,plain,(
% 1.38/0.58    k1_xboole_0 = sK1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 1.38/0.58    inference(trivial_inequality_removal,[],[f94])).
% 1.38/0.58  fof(f94,plain,(
% 1.38/0.58    k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0) | k1_xboole_0 = sK1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 1.38/0.58    inference(duplicate_literal_removal,[],[f89])).
% 1.38/0.58  fof(f89,plain,(
% 1.38/0.58    k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(k1_xboole_0) | k1_xboole_0 = sK1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 1.38/0.58    inference(superposition,[],[f41,f87])).
% 1.38/0.58  fof(f87,plain,(
% 1.38/0.58    ( ! [X0] : (k1_zfmisc_1(k1_xboole_0) = k3_enumset1(X0,X0,X0,X0,X0) | sK1(X0,k1_zfmisc_1(k1_xboole_0)) = X0 | k1_xboole_0 = sK1(X0,k1_zfmisc_1(k1_xboole_0))) )),
% 1.38/0.58    inference(resolution,[],[f68,f24])).
% 1.38/0.58  fof(f68,plain,(
% 1.38/0.58    ( ! [X0,X1] : (r1_tarski(sK1(X0,k1_zfmisc_1(X1)),X1) | k3_enumset1(X0,X0,X0,X0,X0) = k1_zfmisc_1(X1) | sK1(X0,k1_zfmisc_1(X1)) = X0) )),
% 1.38/0.58    inference(resolution,[],[f44,f48])).
% 1.38/0.58  fof(f48,plain,(
% 1.38/0.58    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 1.38/0.58    inference(equality_resolution,[],[f28])).
% 1.38/0.58  fof(f28,plain,(
% 1.38/0.58    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.38/0.58    inference(cnf_transformation,[],[f17])).
% 1.38/0.58  fof(f44,plain,(
% 1.38/0.58    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | sK1(X0,X1) = X0 | k3_enumset1(X0,X0,X0,X0,X0) = X1) )),
% 1.38/0.58    inference(definition_unfolding,[],[f34,f40])).
% 1.38/0.58  fof(f34,plain,(
% 1.38/0.58    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)) )),
% 1.38/0.58    inference(cnf_transformation,[],[f21])).
% 1.38/0.58  fof(f67,plain,(
% 1.38/0.58    ( ! [X2,X3] : (~r2_hidden(sK1(X2,X3),k3_enumset1(X2,X2,X2,X2,X2)) | k3_enumset1(X2,X2,X2,X2,X2) = X3 | ~r2_hidden(X2,X3)) )),
% 1.38/0.58    inference(extensionality_resolution,[],[f51,f52])).
% 1.38/0.58  fof(f52,plain,(
% 1.38/0.58    ( ! [X0,X1] : (sK1(X0,X1) != X0 | k3_enumset1(X0,X0,X0,X0,X0) = X1 | ~r2_hidden(X0,X1)) )),
% 1.38/0.58    inference(inner_rewriting,[],[f43])).
% 1.38/0.58  fof(f43,plain,(
% 1.38/0.58    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X0) = X1 | sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) )),
% 1.38/0.58    inference(definition_unfolding,[],[f35,f40])).
% 1.38/0.58  fof(f35,plain,(
% 1.38/0.58    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) )),
% 1.38/0.58    inference(cnf_transformation,[],[f21])).
% 1.38/0.58  fof(f51,plain,(
% 1.38/0.58    ( ! [X0,X3] : (~r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0)) | X0 = X3) )),
% 1.38/0.58    inference(equality_resolution,[],[f46])).
% 1.38/0.58  fof(f46,plain,(
% 1.38/0.58    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 1.38/0.58    inference(definition_unfolding,[],[f32,f40])).
% 1.38/0.58  fof(f32,plain,(
% 1.38/0.58    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.38/0.58    inference(cnf_transformation,[],[f21])).
% 1.38/0.58  % SZS output end Proof for theBenchmark
% 1.38/0.58  % (15601)------------------------------
% 1.38/0.58  % (15601)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.58  % (15601)Termination reason: Refutation
% 1.38/0.58  
% 1.38/0.58  % (15601)Memory used [KB]: 10746
% 1.38/0.58  % (15601)Time elapsed: 0.121 s
% 1.38/0.58  % (15601)------------------------------
% 1.38/0.58  % (15601)------------------------------
% 1.38/0.58  % (15619)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.58  
% 1.38/0.58  % (15619)Memory used [KB]: 10618
% 1.38/0.58  % (15619)Time elapsed: 0.138 s
% 1.38/0.58  % (15619)------------------------------
% 1.38/0.58  % (15619)------------------------------
% 1.38/0.58  % (15594)Success in time 0.211 s
%------------------------------------------------------------------------------
