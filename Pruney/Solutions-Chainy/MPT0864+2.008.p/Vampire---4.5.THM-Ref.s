%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:31 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 155 expanded)
%              Number of leaves         :   14 (  53 expanded)
%              Depth                    :   14
%              Number of atoms          :  116 ( 287 expanded)
%              Number of equality atoms :   64 ( 212 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f97,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f78,f96])).

fof(f96,plain,(
    ~ spl3_1 ),
    inference(avatar_contradiction_clause,[],[f95])).

fof(f95,plain,
    ( $false
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f94,f35])).

fof(f35,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f94,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl3_1 ),
    inference(superposition,[],[f47,f90])).

fof(f90,plain,
    ( k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f88,f49])).

fof(f49,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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

fof(f88,plain,
    ( ~ r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0))
    | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl3_1 ),
    inference(superposition,[],[f30,f82])).

fof(f82,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK2,sK2,sK2,sK2))
    | ~ spl3_1 ),
    inference(superposition,[],[f44,f81])).

fof(f81,plain,
    ( sK0 = k4_tarski(sK0,sK2)
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f25,f79])).

fof(f79,plain,
    ( sK0 = sK1
    | ~ spl3_1 ),
    inference(backward_demodulation,[],[f51,f56])).

fof(f56,plain,
    ( sK0 = k1_mcart_1(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl3_1
  <=> sK0 = k1_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f51,plain,(
    k1_mcart_1(sK0) = sK1 ),
    inference(superposition,[],[f27,f25])).

fof(f27,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f25,plain,(
    sK0 = k4_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ( sK0 = k2_mcart_1(sK0)
      | sK0 = k1_mcart_1(sK0) )
    & sK0 = k4_tarski(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f21,f20])).

fof(f20,plain,
    ( ? [X0] :
        ( ( k2_mcart_1(X0) = X0
          | k1_mcart_1(X0) = X0 )
        & ? [X1,X2] : k4_tarski(X1,X2) = X0 )
   => ( ( sK0 = k2_mcart_1(sK0)
        | sK0 = k1_mcart_1(sK0) )
      & ? [X2,X1] : k4_tarski(X1,X2) = sK0 ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X2,X1] : k4_tarski(X1,X2) = sK0
   => sK0 = k4_tarski(sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ( k2_mcart_1(X0) = X0
        | k1_mcart_1(X0) = X0 )
      & ? [X1,X2] : k4_tarski(X1,X2) = X0 ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ? [X1,X2] : k4_tarski(X1,X2) = X0
       => ( k2_mcart_1(X0) != X0
          & k1_mcart_1(X0) != X0 ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f44,plain,(
    ! [X0,X1] : k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) = k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f29,f43,f43,f43])).

fof(f43,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f34,f42])).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f39,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f39,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f34,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f29,plain,(
    ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_zfmisc_1)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0))
        & ~ r1_tarski(X0,k2_zfmisc_1(X0,X1)) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k2_zfmisc_1(X1,X0))
        | r1_tarski(X0,k2_zfmisc_1(X0,X1)) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t135_zfmisc_1)).

fof(f47,plain,(
    ! [X0,X1] : ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f40,f42])).

fof(f40,plain,(
    ! [X0,X1] : ~ v1_xboole_0(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : ~ v1_xboole_0(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_xboole_0)).

fof(f78,plain,(
    ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f77])).

fof(f77,plain,
    ( $false
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f76,f35])).

fof(f76,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl3_2 ),
    inference(superposition,[],[f47,f72])).

fof(f72,plain,
    ( k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f71,f49])).

fof(f71,plain,
    ( ~ r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0))
    | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl3_2 ),
    inference(superposition,[],[f31,f64])).

fof(f64,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl3_2 ),
    inference(superposition,[],[f44,f63])).

fof(f63,plain,
    ( sK0 = k4_tarski(sK1,sK0)
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f25,f62])).

fof(f62,plain,
    ( sK0 = sK2
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f52,f60])).

fof(f60,plain,
    ( sK0 = k2_mcart_1(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl3_2
  <=> sK0 = k2_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f52,plain,(
    k2_mcart_1(sK0) = sK2 ),
    inference(superposition,[],[f28,f25])).

fof(f28,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f14])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f61,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f26,f58,f54])).

fof(f26,plain,
    ( sK0 = k2_mcart_1(sK0)
    | sK0 = k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:30:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (19966)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.47  % (19966)Refutation not found, incomplete strategy% (19966)------------------------------
% 0.21/0.47  % (19966)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (19974)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.47  % (19966)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (19966)Memory used [KB]: 10618
% 0.21/0.47  % (19966)Time elapsed: 0.060 s
% 0.21/0.47  % (19966)------------------------------
% 0.21/0.47  % (19966)------------------------------
% 0.21/0.48  % (19974)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f61,f78,f96])).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    ~spl3_1),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f95])).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    $false | ~spl3_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f94,f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    v1_xboole_0(k1_xboole_0)),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    v1_xboole_0(k1_xboole_0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    ~v1_xboole_0(k1_xboole_0) | ~spl3_1),
% 0.21/0.48    inference(superposition,[],[f47,f90])).
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | ~spl3_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f88,f49])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.48    inference(equality_resolution,[],[f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.48    inference(flattening,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.48    inference(nnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    ~r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)) | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | ~spl3_1),
% 0.21/0.48    inference(superposition,[],[f30,f82])).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    k2_enumset1(sK0,sK0,sK0,sK0) = k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK2,sK2,sK2,sK2)) | ~spl3_1),
% 0.21/0.48    inference(superposition,[],[f44,f81])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    sK0 = k4_tarski(sK0,sK2) | ~spl3_1),
% 0.21/0.48    inference(forward_demodulation,[],[f25,f79])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    sK0 = sK1 | ~spl3_1),
% 0.21/0.48    inference(backward_demodulation,[],[f51,f56])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    sK0 = k1_mcart_1(sK0) | ~spl3_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f54])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    spl3_1 <=> sK0 = k1_mcart_1(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    k1_mcart_1(sK0) = sK1),
% 0.21/0.48    inference(superposition,[],[f27,f25])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,axiom,(
% 0.21/0.48    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    sK0 = k4_tarski(sK1,sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    (sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)) & sK0 = k4_tarski(sK1,sK2)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f21,f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0) => ((sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)) & ? [X2,X1] : k4_tarski(X1,X2) = sK0)),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ? [X2,X1] : k4_tarski(X1,X2) = sK0 => sK0 = k4_tarski(sK1,sK2)),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0)),
% 0.21/0.48    inference(ennf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,negated_conjecture,(
% 0.21/0.48    ~! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.21/0.48    inference(negated_conjecture,[],[f15])).
% 0.21/0.48  fof(f15,conjecture,(
% 0.21/0.48    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) = k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f29,f43,f43,f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.48    inference(definition_unfolding,[],[f34,f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.48    inference(definition_unfolding,[],[f39,f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,axiom,(
% 0.21/0.48    ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_zfmisc_1)).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X0,X1)) | k1_xboole_0 = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0,X1] : (k1_xboole_0 = X0 | (~r1_tarski(X0,k2_zfmisc_1(X1,X0)) & ~r1_tarski(X0,k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,axiom,(
% 0.21/0.48    ! [X0,X1] : ((r1_tarski(X0,k2_zfmisc_1(X1,X0)) | r1_tarski(X0,k2_zfmisc_1(X0,X1))) => k1_xboole_0 = X0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t135_zfmisc_1)).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_xboole_0(k2_enumset1(X0,X0,X0,X1))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f40,f42])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_xboole_0(k2_tarski(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0,X1] : ~v1_xboole_0(k2_tarski(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_xboole_0)).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    ~spl3_2),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f77])).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    $false | ~spl3_2),
% 0.21/0.48    inference(subsumption_resolution,[],[f76,f35])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    ~v1_xboole_0(k1_xboole_0) | ~spl3_2),
% 0.21/0.48    inference(superposition,[],[f47,f72])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | ~spl3_2),
% 0.21/0.48    inference(subsumption_resolution,[],[f71,f49])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    ~r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)) | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | ~spl3_2),
% 0.21/0.48    inference(superposition,[],[f31,f64])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    k2_enumset1(sK0,sK0,sK0,sK0) = k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl3_2),
% 0.21/0.48    inference(superposition,[],[f44,f63])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    sK0 = k4_tarski(sK1,sK0) | ~spl3_2),
% 0.21/0.48    inference(backward_demodulation,[],[f25,f62])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    sK0 = sK2 | ~spl3_2),
% 0.21/0.48    inference(forward_demodulation,[],[f52,f60])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    sK0 = k2_mcart_1(sK0) | ~spl3_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f58])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    spl3_2 <=> sK0 = k2_mcart_1(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    k2_mcart_1(sK0) = sK2),
% 0.21/0.48    inference(superposition,[],[f28,f25])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X1,X0)) | k1_xboole_0 = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    spl3_1 | spl3_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f26,f58,f54])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (19974)------------------------------
% 0.21/0.48  % (19974)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (19974)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (19974)Memory used [KB]: 10746
% 0.21/0.48  % (19974)Time elapsed: 0.063 s
% 0.21/0.48  % (19974)------------------------------
% 0.21/0.48  % (19974)------------------------------
% 0.21/0.48  % (19943)Success in time 0.123 s
%------------------------------------------------------------------------------
