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
% DateTime   : Thu Dec  3 12:58:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 102 expanded)
%              Number of leaves         :   14 (  38 expanded)
%              Depth                    :    8
%              Number of atoms          :  100 ( 177 expanded)
%              Number of equality atoms :   24 (  65 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f89,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f45,f49,f63,f85,f88])).

fof(f88,plain,
    ( ~ spl3_5
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f86,f81,f60])).

fof(f60,plain,
    ( spl3_5
  <=> r1_xboole_0(k3_enumset1(k2_mcart_1(sK0),k2_mcart_1(sK0),k2_mcart_1(sK0),k2_mcart_1(sK0),k2_mcart_1(sK0)),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f81,plain,
    ( spl3_8
  <=> r2_hidden(k2_mcart_1(sK0),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f86,plain,
    ( ~ r1_xboole_0(k3_enumset1(k2_mcart_1(sK0),k2_mcart_1(sK0),k2_mcart_1(sK0),k2_mcart_1(sK0),k2_mcart_1(sK0)),k3_enumset1(sK2,sK2,sK2,sK2,sK2))
    | ~ spl3_8 ),
    inference(unit_resulting_resolution,[],[f83,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f21,f28])).

fof(f28,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f18,f27])).

fof(f27,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f19,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f22,f25])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f22,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f19,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f18,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(f83,plain,
    ( r2_hidden(k2_mcart_1(sK0),k3_enumset1(sK2,sK2,sK2,sK2,sK2))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f81])).

fof(f85,plain,
    ( spl3_8
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f73,f42,f81])).

fof(f42,plain,
    ( spl3_3
  <=> r2_hidden(sK0,k2_zfmisc_1(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f73,plain,
    ( r2_hidden(k2_mcart_1(sK0),k3_enumset1(sK2,sK2,sK2,sK2,sK2))
    | ~ spl3_3 ),
    inference(resolution,[],[f44,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f44,plain,
    ( r2_hidden(sK0,k2_zfmisc_1(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f42])).

fof(f63,plain,
    ( spl3_5
    | spl3_2 ),
    inference(avatar_split_clause,[],[f58,f37,f60])).

fof(f37,plain,
    ( spl3_2
  <=> sK2 = k2_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f58,plain,
    ( r1_xboole_0(k3_enumset1(k2_mcart_1(sK0),k2_mcart_1(sK0),k2_mcart_1(sK0),k2_mcart_1(sK0),k2_mcart_1(sK0)),k3_enumset1(sK2,sK2,sK2,sK2,sK2))
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f39,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X1))
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f20,f28,f28])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

fof(f39,plain,
    ( sK2 != k2_mcart_1(sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f49,plain,
    ( spl3_1
    | ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f48])).

fof(f48,plain,
    ( $false
    | spl3_1
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f44,f46])).

fof(f46,plain,
    ( ! [X0] : ~ r2_hidden(sK0,k2_zfmisc_1(sK1,X0))
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f35,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f35,plain,
    ( ~ r2_hidden(k1_mcart_1(sK0),sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl3_1
  <=> r2_hidden(k1_mcart_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f45,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f29,f42])).

fof(f29,plain,(
    r2_hidden(sK0,k2_zfmisc_1(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) ),
    inference(definition_unfolding,[],[f16,f28])).

fof(f16,plain,(
    r2_hidden(sK0,k2_zfmisc_1(sK1,k1_tarski(sK2))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ( sK2 != k2_mcart_1(sK0)
      | ~ r2_hidden(k1_mcart_1(sK0),sK1) )
    & r2_hidden(sK0,k2_zfmisc_1(sK1,k1_tarski(sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( ( k2_mcart_1(X0) != X2
          | ~ r2_hidden(k1_mcart_1(X0),X1) )
        & r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))) )
   => ( ( sK2 != k2_mcart_1(sK0)
        | ~ r2_hidden(k1_mcart_1(sK0),sK1) )
      & r2_hidden(sK0,k2_zfmisc_1(sK1,k1_tarski(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ( k2_mcart_1(X0) != X2
        | ~ r2_hidden(k1_mcart_1(X0),X1) )
      & r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2)))
       => ( k2_mcart_1(X0) = X2
          & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2)))
     => ( k2_mcart_1(X0) = X2
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_mcart_1)).

fof(f40,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f17,f37,f33])).

fof(f17,plain,
    ( sK2 != k2_mcart_1(sK0)
    | ~ r2_hidden(k1_mcart_1(sK0),sK1) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:24:09 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.48  % (19278)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.49  % (19278)Refutation not found, incomplete strategy% (19278)------------------------------
% 0.21/0.49  % (19278)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (19278)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (19278)Memory used [KB]: 10618
% 0.21/0.49  % (19278)Time elapsed: 0.063 s
% 0.21/0.49  % (19278)------------------------------
% 0.21/0.49  % (19278)------------------------------
% 0.21/0.49  % (19286)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.50  % (19286)Refutation not found, incomplete strategy% (19286)------------------------------
% 0.21/0.50  % (19286)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (19286)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (19286)Memory used [KB]: 10618
% 0.21/0.50  % (19286)Time elapsed: 0.072 s
% 0.21/0.50  % (19286)------------------------------
% 0.21/0.50  % (19286)------------------------------
% 0.21/0.51  % (19285)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (19302)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  % (19285)Refutation not found, incomplete strategy% (19285)------------------------------
% 0.21/0.53  % (19285)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (19280)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (19285)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (19285)Memory used [KB]: 10618
% 0.21/0.53  % (19285)Time elapsed: 0.110 s
% 0.21/0.53  % (19285)------------------------------
% 0.21/0.53  % (19285)------------------------------
% 0.21/0.53  % (19302)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f89,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f40,f45,f49,f63,f85,f88])).
% 0.21/0.53  fof(f88,plain,(
% 0.21/0.53    ~spl3_5 | ~spl3_8),
% 0.21/0.53    inference(avatar_split_clause,[],[f86,f81,f60])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    spl3_5 <=> r1_xboole_0(k3_enumset1(k2_mcart_1(sK0),k2_mcart_1(sK0),k2_mcart_1(sK0),k2_mcart_1(sK0),k2_mcart_1(sK0)),k3_enumset1(sK2,sK2,sK2,sK2,sK2))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.53  fof(f81,plain,(
% 0.21/0.53    spl3_8 <=> r2_hidden(k2_mcart_1(sK0),k3_enumset1(sK2,sK2,sK2,sK2,sK2))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.53  fof(f86,plain,(
% 0.21/0.53    ~r1_xboole_0(k3_enumset1(k2_mcart_1(sK0),k2_mcart_1(sK0),k2_mcart_1(sK0),k2_mcart_1(sK0),k2_mcart_1(sK0)),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) | ~spl3_8),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f83,f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f21,f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f18,f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f19,f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f22,f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,plain,(
% 0.21/0.53    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).
% 0.21/0.53  fof(f83,plain,(
% 0.21/0.53    r2_hidden(k2_mcart_1(sK0),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) | ~spl3_8),
% 0.21/0.53    inference(avatar_component_clause,[],[f81])).
% 0.21/0.53  fof(f85,plain,(
% 0.21/0.53    spl3_8 | ~spl3_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f73,f42,f81])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    spl3_3 <=> r2_hidden(sK0,k2_zfmisc_1(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.53  fof(f73,plain,(
% 0.21/0.53    r2_hidden(k2_mcart_1(sK0),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) | ~spl3_3),
% 0.21/0.53    inference(resolution,[],[f44,f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    r2_hidden(sK0,k2_zfmisc_1(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) | ~spl3_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f42])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    spl3_5 | spl3_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f58,f37,f60])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    spl3_2 <=> sK2 = k2_mcart_1(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    r1_xboole_0(k3_enumset1(k2_mcart_1(sK0),k2_mcart_1(sK0),k2_mcart_1(sK0),k2_mcart_1(sK0),k2_mcart_1(sK0)),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) | spl3_2),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f39,f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X1)) | X0 = X1) )),
% 0.21/0.53    inference(definition_unfolding,[],[f20,f28,f28])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,plain,(
% 0.21/0.53    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1] : (X0 != X1 => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    sK2 != k2_mcart_1(sK0) | spl3_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f37])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    spl3_1 | ~spl3_3),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f48])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    $false | (spl3_1 | ~spl3_3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f44,f46])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(sK0,k2_zfmisc_1(sK1,X0))) ) | spl3_1),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f35,f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f13])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ~r2_hidden(k1_mcart_1(sK0),sK1) | spl3_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    spl3_1 <=> r2_hidden(k1_mcart_1(sK0),sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    spl3_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f29,f42])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    r2_hidden(sK0,k2_zfmisc_1(sK1,k3_enumset1(sK2,sK2,sK2,sK2,sK2)))),
% 0.21/0.53    inference(definition_unfolding,[],[f16,f28])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    r2_hidden(sK0,k2_zfmisc_1(sK1,k1_tarski(sK2)))),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    (sK2 != k2_mcart_1(sK0) | ~r2_hidden(k1_mcart_1(sK0),sK1)) & r2_hidden(sK0,k2_zfmisc_1(sK1,k1_tarski(sK2)))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ? [X0,X1,X2] : ((k2_mcart_1(X0) != X2 | ~r2_hidden(k1_mcart_1(X0),X1)) & r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2)))) => ((sK2 != k2_mcart_1(sK0) | ~r2_hidden(k1_mcart_1(sK0),sK1)) & r2_hidden(sK0,k2_zfmisc_1(sK1,k1_tarski(sK2))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f10,plain,(
% 0.21/0.53    ? [X0,X1,X2] : ((k2_mcart_1(X0) != X2 | ~r2_hidden(k1_mcart_1(X0),X1)) & r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))) => (k2_mcart_1(X0) = X2 & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.21/0.53    inference(negated_conjecture,[],[f8])).
% 0.21/0.53  fof(f8,conjecture,(
% 0.21/0.53    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))) => (k2_mcart_1(X0) = X2 & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_mcart_1)).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ~spl3_1 | ~spl3_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f17,f37,f33])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    sK2 != k2_mcart_1(sK0) | ~r2_hidden(k1_mcart_1(sK0),sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (19302)------------------------------
% 0.21/0.53  % (19302)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (19302)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (19302)Memory used [KB]: 6268
% 0.21/0.53  % (19302)Time elapsed: 0.108 s
% 0.21/0.53  % (19302)------------------------------
% 0.21/0.53  % (19302)------------------------------
% 0.21/0.54  % (19275)Success in time 0.176 s
%------------------------------------------------------------------------------
