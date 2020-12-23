%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 106 expanded)
%              Number of leaves         :   16 (  43 expanded)
%              Depth                    :    8
%              Number of atoms          :  138 ( 233 expanded)
%              Number of equality atoms :   66 ( 124 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f133,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f54,f67,f73,f89,f111,f117,f132])).

fof(f132,plain,(
    ~ spl3_10 ),
    inference(avatar_contradiction_clause,[],[f131])).

fof(f131,plain,
    ( $false
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f130,f39])).

fof(f39,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

% (15962)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f130,plain,
    ( ~ r1_tarski(k1_tarski(sK0),k1_tarski(sK0))
    | ~ spl3_10 ),
    inference(superposition,[],[f86,f116])).

fof(f116,plain,
    ( sK0 = k4_tarski(sK0,sK2)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl3_10
  <=> sK0 = k4_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f86,plain,(
    ! [X2,X3] : ~ r1_tarski(k1_tarski(X2),k1_tarski(k4_tarski(X2,X3))) ),
    inference(subsumption_resolution,[],[f84,f77])).

fof(f77,plain,(
    ! [X0] : k1_tarski(X0) != k1_xboole_0 ),
    inference(superposition,[],[f28,f34])).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f28,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f84,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k1_tarski(X2),k1_tarski(k4_tarski(X2,X3)))
      | k1_xboole_0 = k1_tarski(X2) ) ),
    inference(superposition,[],[f32,f27])).

fof(f27,plain,(
    ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_zfmisc_1)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0))
        & ~ r1_tarski(X0,k2_zfmisc_1(X0,X1)) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k2_zfmisc_1(X1,X0))
        | r1_tarski(X0,k2_zfmisc_1(X0,X1)) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t135_zfmisc_1)).

fof(f117,plain,
    ( spl3_10
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f112,f97,f51,f114])).

fof(f51,plain,
    ( spl3_3
  <=> sK0 = k4_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f97,plain,
    ( spl3_8
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f112,plain,
    ( sK0 = k4_tarski(sK0,sK2)
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(backward_demodulation,[],[f53,f99])).

fof(f99,plain,
    ( sK0 = sK1
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f97])).

fof(f53,plain,
    ( sK0 = k4_tarski(sK1,sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f51])).

fof(f111,plain,
    ( spl3_8
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f110,f51,f42,f97])).

fof(f42,plain,
    ( spl3_1
  <=> sK0 = k1_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f110,plain,
    ( sK0 = sK1
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f103,f44])).

fof(f44,plain,
    ( sK0 = k1_mcart_1(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f103,plain,
    ( k1_mcart_1(sK0) = sK1
    | ~ spl3_3 ),
    inference(superposition,[],[f24,f53])).

fof(f24,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f89,plain,(
    ~ spl3_6 ),
    inference(avatar_contradiction_clause,[],[f88])).

fof(f88,plain,
    ( $false
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f87,f39])).

fof(f87,plain,
    ( ~ r1_tarski(k1_tarski(sK0),k1_tarski(sK0))
    | ~ spl3_6 ),
    inference(superposition,[],[f85,f72])).

fof(f72,plain,
    ( sK0 = k4_tarski(sK1,sK0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl3_6
  <=> sK0 = k4_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f85,plain,(
    ! [X0,X1] : ~ r1_tarski(k1_tarski(X1),k1_tarski(k4_tarski(X0,X1))) ),
    inference(subsumption_resolution,[],[f83,f77])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X1),k1_tarski(k4_tarski(X0,X1)))
      | k1_xboole_0 = k1_tarski(X1) ) ),
    inference(superposition,[],[f33,f27])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f73,plain,
    ( spl3_6
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f68,f64,f51,f70])).

fof(f64,plain,
    ( spl3_5
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f68,plain,
    ( sK0 = k4_tarski(sK1,sK0)
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(backward_demodulation,[],[f53,f66])).

fof(f66,plain,
    ( sK0 = sK2
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f64])).

fof(f67,plain,
    ( spl3_5
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f62,f51,f46,f64])).

fof(f46,plain,
    ( spl3_2
  <=> sK0 = k2_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f62,plain,
    ( sK0 = sK2
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f61,f48])).

fof(f48,plain,
    ( sK0 = k2_mcart_1(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f61,plain,
    ( k2_mcart_1(sK0) = sK2
    | ~ spl3_3 ),
    inference(superposition,[],[f25,f53])).

fof(f25,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f12])).

fof(f54,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f22,f51])).

fof(f22,plain,(
    sK0 = k4_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ( sK0 = k2_mcart_1(sK0)
      | sK0 = k1_mcart_1(sK0) )
    & sK0 = k4_tarski(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f18,f17])).

fof(f17,plain,
    ( ? [X0] :
        ( ( k2_mcart_1(X0) = X0
          | k1_mcart_1(X0) = X0 )
        & ? [X1,X2] : k4_tarski(X1,X2) = X0 )
   => ( ( sK0 = k2_mcart_1(sK0)
        | sK0 = k1_mcart_1(sK0) )
      & ? [X2,X1] : k4_tarski(X1,X2) = sK0 ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X2,X1] : k4_tarski(X1,X2) = sK0
   => sK0 = k4_tarski(sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ( k2_mcart_1(X0) = X0
        | k1_mcart_1(X0) = X0 )
      & ? [X1,X2] : k4_tarski(X1,X2) = X0 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ? [X1,X2] : k4_tarski(X1,X2) = X0
       => ( k2_mcart_1(X0) != X0
          & k1_mcart_1(X0) != X0 ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f49,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f23,f46,f42])).

fof(f23,plain,
    ( sK0 = k2_mcart_1(sK0)
    | sK0 = k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:06:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (15978)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.51  % (15969)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.51  % (15961)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (15978)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f133,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f49,f54,f67,f73,f89,f111,f117,f132])).
% 0.21/0.52  fof(f132,plain,(
% 0.21/0.52    ~spl3_10),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f131])).
% 0.21/0.52  fof(f131,plain,(
% 0.21/0.52    $false | ~spl3_10),
% 0.21/0.52    inference(subsumption_resolution,[],[f130,f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.52    inference(equality_resolution,[],[f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.52    inference(flattening,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f1])).
% 0.21/0.52  % (15962)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.52  fof(f130,plain,(
% 0.21/0.52    ~r1_tarski(k1_tarski(sK0),k1_tarski(sK0)) | ~spl3_10),
% 0.21/0.52    inference(superposition,[],[f86,f116])).
% 0.21/0.52  fof(f116,plain,(
% 0.21/0.52    sK0 = k4_tarski(sK0,sK2) | ~spl3_10),
% 0.21/0.52    inference(avatar_component_clause,[],[f114])).
% 0.21/0.52  fof(f114,plain,(
% 0.21/0.52    spl3_10 <=> sK0 = k4_tarski(sK0,sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.52  fof(f86,plain,(
% 0.21/0.52    ( ! [X2,X3] : (~r1_tarski(k1_tarski(X2),k1_tarski(k4_tarski(X2,X3)))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f84,f77])).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    ( ! [X0] : (k1_tarski(X0) != k1_xboole_0) )),
% 0.21/0.52    inference(superposition,[],[f28,f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    ( ! [X2,X3] : (~r1_tarski(k1_tarski(X2),k1_tarski(k4_tarski(X2,X3))) | k1_xboole_0 = k1_tarski(X2)) )),
% 0.21/0.52    inference(superposition,[],[f32,f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_zfmisc_1)).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X0,X1)) | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0,X1] : (k1_xboole_0 = X0 | (~r1_tarski(X0,k2_zfmisc_1(X1,X0)) & ~r1_tarski(X0,k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1] : ((r1_tarski(X0,k2_zfmisc_1(X1,X0)) | r1_tarski(X0,k2_zfmisc_1(X0,X1))) => k1_xboole_0 = X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t135_zfmisc_1)).
% 0.21/0.52  fof(f117,plain,(
% 0.21/0.52    spl3_10 | ~spl3_3 | ~spl3_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f112,f97,f51,f114])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    spl3_3 <=> sK0 = k4_tarski(sK1,sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.52  fof(f97,plain,(
% 0.21/0.52    spl3_8 <=> sK0 = sK1),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.52  fof(f112,plain,(
% 0.21/0.52    sK0 = k4_tarski(sK0,sK2) | (~spl3_3 | ~spl3_8)),
% 0.21/0.52    inference(backward_demodulation,[],[f53,f99])).
% 0.21/0.52  fof(f99,plain,(
% 0.21/0.52    sK0 = sK1 | ~spl3_8),
% 0.21/0.52    inference(avatar_component_clause,[],[f97])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    sK0 = k4_tarski(sK1,sK2) | ~spl3_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f51])).
% 0.21/0.52  fof(f111,plain,(
% 0.21/0.52    spl3_8 | ~spl3_1 | ~spl3_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f110,f51,f42,f97])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    spl3_1 <=> sK0 = k1_mcart_1(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.52  fof(f110,plain,(
% 0.21/0.52    sK0 = sK1 | (~spl3_1 | ~spl3_3)),
% 0.21/0.52    inference(forward_demodulation,[],[f103,f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    sK0 = k1_mcart_1(sK0) | ~spl3_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f42])).
% 0.21/0.52  fof(f103,plain,(
% 0.21/0.52    k1_mcart_1(sK0) = sK1 | ~spl3_3),
% 0.21/0.52    inference(superposition,[],[f24,f53])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,axiom,(
% 0.21/0.52    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.21/0.52  fof(f89,plain,(
% 0.21/0.52    ~spl3_6),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f88])).
% 0.21/0.52  fof(f88,plain,(
% 0.21/0.52    $false | ~spl3_6),
% 0.21/0.52    inference(subsumption_resolution,[],[f87,f39])).
% 0.21/0.52  fof(f87,plain,(
% 0.21/0.52    ~r1_tarski(k1_tarski(sK0),k1_tarski(sK0)) | ~spl3_6),
% 0.21/0.52    inference(superposition,[],[f85,f72])).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    sK0 = k4_tarski(sK1,sK0) | ~spl3_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f70])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    spl3_6 <=> sK0 = k4_tarski(sK1,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.52  fof(f85,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X1),k1_tarski(k4_tarski(X0,X1)))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f83,f77])).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X1),k1_tarski(k4_tarski(X0,X1))) | k1_xboole_0 = k1_tarski(X1)) )),
% 0.21/0.52    inference(superposition,[],[f33,f27])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X1,X0)) | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    spl3_6 | ~spl3_3 | ~spl3_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f68,f64,f51,f70])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    spl3_5 <=> sK0 = sK2),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    sK0 = k4_tarski(sK1,sK0) | (~spl3_3 | ~spl3_5)),
% 0.21/0.52    inference(backward_demodulation,[],[f53,f66])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    sK0 = sK2 | ~spl3_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f64])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    spl3_5 | ~spl3_2 | ~spl3_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f62,f51,f46,f64])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    spl3_2 <=> sK0 = k2_mcart_1(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    sK0 = sK2 | (~spl3_2 | ~spl3_3)),
% 0.21/0.52    inference(forward_demodulation,[],[f61,f48])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    sK0 = k2_mcart_1(sK0) | ~spl3_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f46])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    k2_mcart_1(sK0) = sK2 | ~spl3_3),
% 0.21/0.52    inference(superposition,[],[f25,f53])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    spl3_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f22,f51])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    sK0 = k4_tarski(sK1,sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    (sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)) & sK0 = k4_tarski(sK1,sK2)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f18,f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0) => ((sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)) & ? [X2,X1] : k4_tarski(X1,X2) = sK0)),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ? [X2,X1] : k4_tarski(X1,X2) = sK0 => sK0 = k4_tarski(sK1,sK2)),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0)),
% 0.21/0.52    inference(ennf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,negated_conjecture,(
% 0.21/0.52    ~! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.21/0.52    inference(negated_conjecture,[],[f13])).
% 0.21/0.52  fof(f13,conjecture,(
% 0.21/0.52    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    spl3_1 | spl3_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f23,f46,f42])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (15978)------------------------------
% 0.21/0.52  % (15978)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (15978)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (15978)Memory used [KB]: 6268
% 0.21/0.52  % (15978)Time elapsed: 0.067 s
% 0.21/0.52  % (15978)------------------------------
% 0.21/0.52  % (15978)------------------------------
% 0.21/0.52  % (15964)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.52  % (15955)Success in time 0.158 s
%------------------------------------------------------------------------------
