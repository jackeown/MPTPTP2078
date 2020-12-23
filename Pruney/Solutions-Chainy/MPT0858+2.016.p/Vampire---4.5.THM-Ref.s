%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:19 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   29 (  43 expanded)
%              Number of leaves         :    7 (  15 expanded)
%              Depth                    :    6
%              Number of atoms          :   61 (  86 expanded)
%              Number of equality atoms :   22 (  36 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f43,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f29,f34,f40,f42])).

fof(f42,plain,
    ( spl3_2
    | ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f41])).

fof(f41,plain,
    ( $false
    | spl3_2
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f33,f28,f20])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X1),X2))
      | k1_mcart_1(X0) = X1 ) ),
    inference(definition_unfolding,[],[f14,f11])).

fof(f11,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f14,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
      | k1_mcart_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 )
      | ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).

fof(f28,plain,
    ( sK1 != k1_mcart_1(sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f26])).

fof(f26,plain,
    ( spl3_2
  <=> sK1 = k1_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f33,plain,
    ( r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK1),k2_tarski(sK2,sK2)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f31])).

fof(f31,plain,
    ( spl3_3
  <=> r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK1),k2_tarski(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f40,plain,
    ( spl3_1
    | ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f35])).

fof(f35,plain,
    ( $false
    | spl3_1
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f24,f33,f17])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X2)))
      | k2_mcart_1(X0) = X2 ) ),
    inference(definition_unfolding,[],[f13,f11])).

fof(f13,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2)))
      | k2_mcart_1(X0) = X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( ( k2_mcart_1(X0) = X2
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2)))
     => ( k2_mcart_1(X0) = X2
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_mcart_1)).

% (9921)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
fof(f24,plain,
    ( sK2 != k2_mcart_1(sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f22])).

fof(f22,plain,
    ( spl3_1
  <=> sK2 = k2_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f34,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f16,f31])).

fof(f16,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK1),k2_tarski(sK2,sK2))) ),
    inference(definition_unfolding,[],[f10,f11,f11])).

fof(f10,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),k1_tarski(sK2))) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ( k2_mcart_1(X0) != X2
        | k1_mcart_1(X0) != X1 )
      & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2)))
       => ( k2_mcart_1(X0) = X2
          & k1_mcart_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2)))
     => ( k2_mcart_1(X0) = X2
        & k1_mcart_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_mcart_1)).

fof(f29,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f9,f26,f22])).

fof(f9,plain,
    ( sK1 != k1_mcart_1(sK0)
    | sK2 != k2_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:59:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.52  % (9938)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (9929)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (9938)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f29,f34,f40,f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    spl3_2 | ~spl3_3),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    $false | (spl3_2 | ~spl3_3)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f33,f28,f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X1),X2)) | k1_mcart_1(X0) = X1) )),
% 0.21/0.53    inference(definition_unfolding,[],[f14,f11])).
% 0.21/0.53  fof(f11,plain,(
% 0.21/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) | k1_mcart_1(X0) = X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1) | ~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)))),
% 0.21/0.53    inference(ennf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) => (r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    sK1 != k1_mcart_1(sK0) | spl3_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    spl3_2 <=> sK1 = k1_mcart_1(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK1),k2_tarski(sK2,sK2))) | ~spl3_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    spl3_3 <=> r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK1),k2_tarski(sK2,sK2)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    spl3_1 | ~spl3_3),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    $false | (spl3_1 | ~spl3_3)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f24,f33,f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X2))) | k2_mcart_1(X0) = X2) )),
% 0.21/0.53    inference(definition_unfolding,[],[f13,f11])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))) | k2_mcart_1(X0) = X2) )),
% 0.21/0.53    inference(cnf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((k2_mcart_1(X0) = X2 & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))))),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))) => (k2_mcart_1(X0) = X2 & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_mcart_1)).
% 0.21/0.53  % (9921)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    sK2 != k2_mcart_1(sK0) | spl3_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    spl3_1 <=> sK2 = k2_mcart_1(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    spl3_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f16,f31])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK1),k2_tarski(sK2,sK2)))),
% 0.21/0.53    inference(definition_unfolding,[],[f10,f11,f11])).
% 0.21/0.53  fof(f10,plain,(
% 0.21/0.53    r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),k1_tarski(sK2)))),
% 0.21/0.53    inference(cnf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,plain,(
% 0.21/0.53    ? [X0,X1,X2] : ((k2_mcart_1(X0) != X2 | k1_mcart_1(X0) != X1) & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2))))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2))) => (k2_mcart_1(X0) = X2 & k1_mcart_1(X0) = X1))),
% 0.21/0.53    inference(negated_conjecture,[],[f4])).
% 0.21/0.53  fof(f4,conjecture,(
% 0.21/0.53    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2))) => (k2_mcart_1(X0) = X2 & k1_mcart_1(X0) = X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_mcart_1)).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ~spl3_1 | ~spl3_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f9,f26,f22])).
% 0.21/0.53  fof(f9,plain,(
% 0.21/0.53    sK1 != k1_mcart_1(sK0) | sK2 != k2_mcart_1(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f6])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (9938)------------------------------
% 0.21/0.53  % (9938)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (9938)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (9938)Memory used [KB]: 10618
% 0.21/0.53  % (9938)Time elapsed: 0.062 s
% 0.21/0.53  % (9938)------------------------------
% 0.21/0.53  % (9938)------------------------------
% 0.21/0.53  % (9910)Success in time 0.174 s
%------------------------------------------------------------------------------
