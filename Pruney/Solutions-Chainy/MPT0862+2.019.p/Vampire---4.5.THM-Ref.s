%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:29 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 113 expanded)
%              Number of leaves         :   11 (  39 expanded)
%              Depth                    :    8
%              Number of atoms          :   88 ( 189 expanded)
%              Number of equality atoms :   45 ( 131 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f142,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f54,f96,f114])).

fof(f114,plain,
    ( spl4_1
    | spl4_3 ),
    inference(avatar_contradiction_clause,[],[f106])).

fof(f106,plain,
    ( $false
    | spl4_1
    | spl4_3 ),
    inference(unit_resulting_resolution,[],[f40,f29,f53,f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,k2_enumset1(X2,X2,X2,X3)))
      | k2_mcart_1(X0) = X2
      | k2_mcart_1(X0) = X3 ) ),
    inference(definition_unfolding,[],[f16,f27])).

fof(f27,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f23,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f23,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f16,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3)))
      | k2_mcart_1(X0) = X2
      | k2_mcart_1(X0) = X3 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k2_mcart_1(X0) = X3
          | k2_mcart_1(X0) = X2 )
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3)))
     => ( ( k2_mcart_1(X0) = X3
          | k2_mcart_1(X0) = X2 )
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_mcart_1)).

fof(f53,plain,
    ( sK3 != k2_mcart_1(sK0)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl4_3
  <=> sK3 = k2_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f29,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK2,sK2,sK2,sK3))) ),
    inference(definition_unfolding,[],[f15,f28,f27])).

fof(f28,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f20,f27])).

fof(f20,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f15,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),k2_tarski(sK2,sK3))) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ( k2_mcart_1(X0) != X3
          & k2_mcart_1(X0) != X2 )
        | k1_mcart_1(X0) != X1 )
      & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)))
       => ( ( k2_mcart_1(X0) = X3
            | k2_mcart_1(X0) = X2 )
          & k1_mcart_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)))
     => ( ( k2_mcart_1(X0) = X3
          | k2_mcart_1(X0) = X2 )
        & k1_mcart_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_mcart_1)).

fof(f40,plain,
    ( sK2 != k2_mcart_1(sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl4_1
  <=> sK2 = k2_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f96,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f93])).

fof(f93,plain,
    ( $false
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f61,f55,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) != X0
      | ~ r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f22,f28])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f55,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(k1_mcart_1(sK0),k1_mcart_1(sK0),k1_mcart_1(sK0),k1_mcart_1(sK0)))
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f44,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X0,X0,X0,X0) = k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f24,f28,f28,f28])).

fof(f24,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f44,plain,
    ( sK1 != k1_mcart_1(sK0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl4_2
  <=> sK1 = k1_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f61,plain,(
    r2_hidden(k1_mcart_1(sK0),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(unit_resulting_resolution,[],[f29,f18])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f54,plain,
    ( ~ spl4_3
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f14,f42,f51])).

fof(f14,plain,
    ( sK1 != k1_mcart_1(sK0)
    | sK3 != k2_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f45,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f13,f42,f38])).

fof(f13,plain,
    ( sK1 != k1_mcart_1(sK0)
    | sK2 != k2_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:06:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.45  % (3156)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.47  % (3156)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.48  % (3180)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.48  % (3172)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f142,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f45,f54,f96,f114])).
% 0.20/0.48  fof(f114,plain,(
% 0.20/0.48    spl4_1 | spl4_3),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f106])).
% 0.20/0.48  fof(f106,plain,(
% 0.20/0.48    $false | (spl4_1 | spl4_3)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f40,f29,f53,f31])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,k2_enumset1(X2,X2,X2,X3))) | k2_mcart_1(X0) = X2 | k2_mcart_1(X0) = X3) )),
% 0.20/0.48    inference(definition_unfolding,[],[f16,f27])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.20/0.48    inference(definition_unfolding,[],[f23,f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))) | k2_mcart_1(X0) = X2 | k2_mcart_1(X0) = X3) )),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ! [X0,X1,X2,X3] : (((k2_mcart_1(X0) = X3 | k2_mcart_1(X0) = X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))))),
% 0.20/0.48    inference(ennf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,axiom,(
% 0.20/0.48    ! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))) => ((k2_mcart_1(X0) = X3 | k2_mcart_1(X0) = X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_mcart_1)).
% 0.20/0.48  fof(f53,plain,(
% 0.20/0.48    sK3 != k2_mcart_1(sK0) | spl4_3),
% 0.20/0.48    inference(avatar_component_clause,[],[f51])).
% 0.20/0.48  fof(f51,plain,(
% 0.20/0.48    spl4_3 <=> sK3 = k2_mcart_1(sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    r2_hidden(sK0,k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK2,sK2,sK2,sK3)))),
% 0.20/0.48    inference(definition_unfolding,[],[f15,f28,f27])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.20/0.48    inference(definition_unfolding,[],[f20,f27])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),k2_tarski(sK2,sK3)))),
% 0.20/0.48    inference(cnf_transformation,[],[f10])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    ? [X0,X1,X2,X3] : (((k2_mcart_1(X0) != X3 & k2_mcart_1(X0) != X2) | k1_mcart_1(X0) != X1) & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))))),
% 0.20/0.48    inference(ennf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))) => ((k2_mcart_1(X0) = X3 | k2_mcart_1(X0) = X2) & k1_mcart_1(X0) = X1))),
% 0.20/0.48    inference(negated_conjecture,[],[f8])).
% 0.20/0.48  fof(f8,conjecture,(
% 0.20/0.48    ! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))) => ((k2_mcart_1(X0) = X3 | k2_mcart_1(X0) = X2) & k1_mcart_1(X0) = X1))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_mcart_1)).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    sK2 != k2_mcart_1(sK0) | spl4_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f38])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    spl4_1 <=> sK2 = k2_mcart_1(sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.48  fof(f96,plain,(
% 0.20/0.48    spl4_2),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f93])).
% 0.20/0.48  fof(f93,plain,(
% 0.20/0.48    $false | spl4_2),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f61,f55,f32])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) != X0 | ~r2_hidden(X1,X0)) )),
% 0.20/0.48    inference(definition_unfolding,[],[f22,f28])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.20/0.48  fof(f55,plain,(
% 0.20/0.48    k2_enumset1(sK1,sK1,sK1,sK1) = k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(k1_mcart_1(sK0),k1_mcart_1(sK0),k1_mcart_1(sK0),k1_mcart_1(sK0))) | spl4_2),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f44,f35])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X0) = k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) | X0 = X1) )),
% 0.20/0.48    inference(definition_unfolding,[],[f24,f28,f28,f28])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ( ! [X0,X1] : (X0 = X1 | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    sK1 != k1_mcart_1(sK0) | spl4_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f42])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    spl4_2 <=> sK1 = k1_mcart_1(sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.48  fof(f61,plain,(
% 0.20/0.48    r2_hidden(k1_mcart_1(sK0),k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f29,f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.20/0.48  fof(f54,plain,(
% 0.20/0.48    ~spl4_3 | ~spl4_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f14,f42,f51])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    sK1 != k1_mcart_1(sK0) | sK3 != k2_mcart_1(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f10])).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    ~spl4_1 | ~spl4_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f13,f42,f38])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    sK1 != k1_mcart_1(sK0) | sK2 != k2_mcart_1(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f10])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (3156)------------------------------
% 0.20/0.48  % (3156)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (3156)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (3156)Memory used [KB]: 6268
% 0.20/0.48  % (3156)Time elapsed: 0.091 s
% 0.20/0.48  % (3156)------------------------------
% 0.20/0.48  % (3156)------------------------------
% 0.20/0.49  % (3151)Success in time 0.131 s
%------------------------------------------------------------------------------
