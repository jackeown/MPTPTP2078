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
% DateTime   : Thu Dec  3 12:37:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 276 expanded)
%              Number of leaves         :   14 (  78 expanded)
%              Depth                    :   16
%              Number of atoms          :  148 ( 653 expanded)
%              Number of equality atoms :   75 ( 419 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f326,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f134,f201,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f37,f47])).

fof(f47,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f33,f46])).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f35,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f35,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f33,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f201,plain,(
    ~ r1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0) ),
    inference(subsumption_resolution,[],[f200,f76])).

fof(f76,plain,(
    k1_xboole_0 != sK0 ),
    inference(subsumption_resolution,[],[f57,f31])).

fof(f31,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f57,plain,
    ( k1_xboole_0 != sK0
    | ~ r1_tarski(k1_xboole_0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(inner_rewriting,[],[f49])).

fof(f49,plain,
    ( k1_xboole_0 != sK0
    | ~ r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f29,f47])).

fof(f29,plain,
    ( k1_xboole_0 != sK0
    | ~ r1_tarski(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ( ( sK0 != k1_tarski(sK1)
        & k1_xboole_0 != sK0 )
      | ~ r1_tarski(sK0,k1_tarski(sK1)) )
    & ( sK0 = k1_tarski(sK1)
      | k1_xboole_0 = sK0
      | r1_tarski(sK0,k1_tarski(sK1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f23])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( ( ( k1_tarski(X1) != X0
            & k1_xboole_0 != X0 )
          | ~ r1_tarski(X0,k1_tarski(X1)) )
        & ( k1_tarski(X1) = X0
          | k1_xboole_0 = X0
          | r1_tarski(X0,k1_tarski(X1)) ) )
   => ( ( ( sK0 != k1_tarski(sK1)
          & k1_xboole_0 != sK0 )
        | ~ r1_tarski(sK0,k1_tarski(sK1)) )
      & ( sK0 = k1_tarski(sK1)
        | k1_xboole_0 = sK0
        | r1_tarski(sK0,k1_tarski(sK1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ( ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 )
        | ~ r1_tarski(X0,k1_tarski(X1)) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ( ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 )
        | ~ r1_tarski(X0,k1_tarski(X1)) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <~> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,k1_tarski(X1))
      <=> ( k1_tarski(X1) = X0
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_zfmisc_1)).

fof(f200,plain,
    ( k1_xboole_0 = sK0
    | ~ r1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0) ),
    inference(forward_demodulation,[],[f185,f32])).

fof(f32,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f185,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k1_xboole_0)
    | ~ r1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0) ),
    inference(superposition,[],[f175,f117])).

fof(f117,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(unit_resulting_resolution,[],[f114,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

% (1828)Termination reason: Refutation not found, incomplete strategy
fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f114,plain,(
    r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(subsumption_resolution,[],[f113,f76])).

% (1828)Memory used [KB]: 10618
fof(f113,plain,
    ( k1_xboole_0 = sK0
    | r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(subsumption_resolution,[],[f50,f72])).

% (1828)Time elapsed: 0.099 s
% (1828)------------------------------
% (1828)------------------------------
fof(f72,plain,(
    sK0 != k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(subsumption_resolution,[],[f56,f54])).

fof(f54,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f56,plain,
    ( sK0 != k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ r1_tarski(sK0,sK0) ),
    inference(inner_rewriting,[],[f48])).

fof(f48,plain,
    ( sK0 != k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f30,f47,f47])).

fof(f30,plain,
    ( sK0 != k1_tarski(sK1)
    | ~ r1_tarski(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f50,plain,
    ( sK0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | k1_xboole_0 = sK0
    | r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f28,f47,f47])).

fof(f28,plain,
    ( sK0 = k1_tarski(sK1)
    | k1_xboole_0 = sK0
    | r1_tarski(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f175,plain,(
    ! [X4,X3] :
      ( k1_xboole_0 = k4_xboole_0(X4,k4_xboole_0(X4,X3))
      | ~ r1_xboole_0(X3,X4) ) ),
    inference(forward_demodulation,[],[f81,f62])).

fof(f62,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(unit_resulting_resolution,[],[f54,f44])).

fof(f81,plain,(
    ! [X4,X3] :
      ( k4_xboole_0(X4,k4_xboole_0(X4,X3)) = k4_xboole_0(X3,X3)
      | ~ r1_xboole_0(X3,X4) ) ),
    inference(superposition,[],[f51,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(X0,X1) = X0 ) ),
    inference(unused_predicate_definition_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f34,f36,f36])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f134,plain,(
    ~ r2_hidden(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f115,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f42,f47])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_tarski(X0),X1) ) ),
    inference(unused_predicate_definition_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f115,plain,(
    ~ r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f72,f114,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:33:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (1819)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.50  % (1819)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (1820)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (1838)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.51  % (1839)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.51  % (1828)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.51  % (1828)Refutation not found, incomplete strategy% (1828)------------------------------
% 0.21/0.51  % (1828)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (1829)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f326,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f134,f201,f52])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f37,f47])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f33,f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f35,f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,axiom,(
% 0.21/0.52    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.21/0.52  fof(f201,plain,(
% 0.21/0.52    ~r1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f200,f76])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    k1_xboole_0 != sK0),
% 0.21/0.52    inference(subsumption_resolution,[],[f57,f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    k1_xboole_0 != sK0 | ~r1_tarski(k1_xboole_0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.21/0.52    inference(inner_rewriting,[],[f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    k1_xboole_0 != sK0 | ~r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.21/0.52    inference(definition_unfolding,[],[f29,f47])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    k1_xboole_0 != sK0 | ~r1_tarski(sK0,k1_tarski(sK1))),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ((sK0 != k1_tarski(sK1) & k1_xboole_0 != sK0) | ~r1_tarski(sK0,k1_tarski(sK1))) & (sK0 = k1_tarski(sK1) | k1_xboole_0 = sK0 | r1_tarski(sK0,k1_tarski(sK1)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ? [X0,X1] : (((k1_tarski(X1) != X0 & k1_xboole_0 != X0) | ~r1_tarski(X0,k1_tarski(X1))) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | r1_tarski(X0,k1_tarski(X1)))) => (((sK0 != k1_tarski(sK1) & k1_xboole_0 != sK0) | ~r1_tarski(sK0,k1_tarski(sK1))) & (sK0 = k1_tarski(sK1) | k1_xboole_0 = sK0 | r1_tarski(sK0,k1_tarski(sK1))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ? [X0,X1] : (((k1_tarski(X1) != X0 & k1_xboole_0 != X0) | ~r1_tarski(X0,k1_tarski(X1))) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | r1_tarski(X0,k1_tarski(X1))))),
% 0.21/0.52    inference(flattening,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ? [X0,X1] : (((k1_tarski(X1) != X0 & k1_xboole_0 != X0) | ~r1_tarski(X0,k1_tarski(X1))) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | r1_tarski(X0,k1_tarski(X1))))),
% 0.21/0.52    inference(nnf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ? [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <~> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.21/0.52    inference(negated_conjecture,[],[f13])).
% 0.21/0.52  fof(f13,conjecture,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_zfmisc_1)).
% 0.21/0.52  fof(f200,plain,(
% 0.21/0.52    k1_xboole_0 = sK0 | ~r1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0)),
% 0.21/0.52    inference(forward_demodulation,[],[f185,f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.52  fof(f185,plain,(
% 0.21/0.52    k1_xboole_0 = k4_xboole_0(sK0,k1_xboole_0) | ~r1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0)),
% 0.21/0.52    inference(superposition,[],[f175,f117])).
% 0.21/0.52  fof(f117,plain,(
% 0.21/0.52    k1_xboole_0 = k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f114,f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.21/0.52    inference(nnf_transformation,[],[f3])).
% 0.21/0.52  % (1828)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.52  
% 0.21/0.52  fof(f114,plain,(
% 0.21/0.52    r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.21/0.52    inference(subsumption_resolution,[],[f113,f76])).
% 0.21/0.52  % (1828)Memory used [KB]: 10618
% 0.21/0.52  fof(f113,plain,(
% 0.21/0.52    k1_xboole_0 = sK0 | r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.21/0.52    inference(subsumption_resolution,[],[f50,f72])).
% 0.21/0.52  % (1828)Time elapsed: 0.099 s
% 0.21/0.52  % (1828)------------------------------
% 0.21/0.52  % (1828)------------------------------
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    sK0 != k2_enumset1(sK1,sK1,sK1,sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f56,f54])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.52    inference(equality_resolution,[],[f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.52    inference(flattening,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    sK0 != k2_enumset1(sK1,sK1,sK1,sK1) | ~r1_tarski(sK0,sK0)),
% 0.21/0.52    inference(inner_rewriting,[],[f48])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    sK0 != k2_enumset1(sK1,sK1,sK1,sK1) | ~r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.21/0.52    inference(definition_unfolding,[],[f30,f47,f47])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    sK0 != k1_tarski(sK1) | ~r1_tarski(sK0,k1_tarski(sK1))),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    sK0 = k2_enumset1(sK1,sK1,sK1,sK1) | k1_xboole_0 = sK0 | r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.21/0.52    inference(definition_unfolding,[],[f28,f47,f47])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    sK0 = k1_tarski(sK1) | k1_xboole_0 = sK0 | r1_tarski(sK0,k1_tarski(sK1))),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f175,plain,(
% 0.21/0.52    ( ! [X4,X3] : (k1_xboole_0 = k4_xboole_0(X4,k4_xboole_0(X4,X3)) | ~r1_xboole_0(X3,X4)) )),
% 0.21/0.52    inference(forward_demodulation,[],[f81,f62])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f54,f44])).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    ( ! [X4,X3] : (k4_xboole_0(X4,k4_xboole_0(X4,X3)) = k4_xboole_0(X3,X3) | ~r1_xboole_0(X3,X4)) )),
% 0.21/0.52    inference(superposition,[],[f51,f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(X0,X1) = X0)),
% 0.21/0.52    inference(unused_predicate_definition_removal,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.21/0.52    inference(definition_unfolding,[],[f34,f36,f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.52  fof(f134,plain,(
% 0.21/0.52    ~r2_hidden(sK1,sK0)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f115,f53])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f42,f47])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_tarski(X0),X1))),
% 0.21/0.52    inference(unused_predicate_definition_removal,[],[f11])).
% 0.21/0.52  fof(f11,axiom,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.21/0.52  fof(f115,plain,(
% 0.21/0.52    ~r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),sK0)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f72,f114,f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f26])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (1819)------------------------------
% 0.21/0.52  % (1819)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (1819)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (1819)Memory used [KB]: 1791
% 0.21/0.52  % (1819)Time elapsed: 0.091 s
% 0.21/0.52  % (1819)------------------------------
% 0.21/0.52  % (1819)------------------------------
% 0.21/0.52  % (1824)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.52  % (1807)Success in time 0.163 s
%------------------------------------------------------------------------------
