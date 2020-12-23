%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:24 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   48 (  99 expanded)
%              Number of leaves         :   12 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :  104 ( 190 expanded)
%              Number of equality atoms :   49 ( 109 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f85,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f56,f68,f73,f78,f84])).

fof(f84,plain,
    ( spl5_2
    | spl5_4
    | ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f79])).

fof(f79,plain,
    ( $false
    | spl5_2
    | spl5_4
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f50,f72,f77,f42])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X1))
      | X1 = X3
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k3_enumset1(X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f20,f27])).

fof(f27,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f15,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f16,f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f16,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

% (6464)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
fof(f15,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f77,plain,
    ( r2_hidden(k1_mcart_1(sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK2))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl5_5
  <=> r2_hidden(k1_mcart_1(sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f72,plain,
    ( sK2 != k1_mcart_1(sK0)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl5_4
  <=> sK2 = k1_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f50,plain,
    ( sK1 != k1_mcart_1(sK0)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl5_2
  <=> sK1 = k1_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f78,plain,
    ( spl5_5
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f59,f53,f75])).

fof(f53,plain,
    ( spl5_3
  <=> r2_hidden(sK0,k2_zfmisc_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f59,plain,
    ( r2_hidden(k1_mcart_1(sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK2))
    | ~ spl5_3 ),
    inference(resolution,[],[f55,f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,k3_enumset1(X2,X2,X2,X2,X3)))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(definition_unfolding,[],[f25,f27])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3)))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k2_mcart_1(X0) = X3
          | k2_mcart_1(X0) = X2 )
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3)))
     => ( ( k2_mcart_1(X0) = X3
          | k2_mcart_1(X0) = X2 )
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_mcart_1)).

fof(f55,plain,
    ( r2_hidden(sK0,k2_zfmisc_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f53])).

fof(f73,plain,
    ( ~ spl5_1
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f12,f70,f44])).

fof(f44,plain,
    ( spl5_1
  <=> sK3 = k2_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f12,plain,
    ( sK2 != k1_mcart_1(sK0)
    | sK3 != k2_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( ( k2_mcart_1(X0) != X3
        | ( k1_mcart_1(X0) != X2
          & k1_mcart_1(X0) != X1 ) )
      & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)))
       => ( k2_mcart_1(X0) = X3
          & ( k1_mcart_1(X0) = X2
            | k1_mcart_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)))
     => ( k2_mcart_1(X0) = X3
        & ( k1_mcart_1(X0) = X2
          | k1_mcart_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_mcart_1)).

fof(f68,plain,
    ( spl5_1
    | ~ spl5_3 ),
    inference(avatar_contradiction_clause,[],[f57])).

fof(f57,plain,
    ( $false
    | spl5_1
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f46,f46,f55,f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,k3_enumset1(X2,X2,X2,X2,X3)))
      | k2_mcart_1(X0) = X2
      | k2_mcart_1(X0) = X3 ) ),
    inference(definition_unfolding,[],[f24,f27])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3)))
      | k2_mcart_1(X0) = X2
      | k2_mcart_1(X0) = X3 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f46,plain,
    ( sK3 != k2_mcart_1(sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f44])).

fof(f56,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f29,f53])).

fof(f29,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))) ),
    inference(definition_unfolding,[],[f13,f27,f28])).

fof(f28,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f14,f27])).

fof(f14,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f13,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k1_tarski(sK3))) ),
    inference(cnf_transformation,[],[f9])).

fof(f51,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f11,f48,f44])).

fof(f11,plain,
    ( sK1 != k1_mcart_1(sK0)
    | sK3 != k2_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:36:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (6465)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.48  % (6491)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.49  % (6473)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.50  % (6467)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.50  % (6475)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.50  % (6491)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f85,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f51,f56,f68,f73,f78,f84])).
% 0.20/0.50  fof(f84,plain,(
% 0.20/0.50    spl5_2 | spl5_4 | ~spl5_5),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f79])).
% 0.20/0.50  fof(f79,plain,(
% 0.20/0.50    $false | (spl5_2 | spl5_4 | ~spl5_5)),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f50,f72,f77,f42])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    ( ! [X0,X3,X1] : (~r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X1)) | X1 = X3 | X0 = X3) )),
% 0.20/0.50    inference(equality_resolution,[],[f32])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k3_enumset1(X0,X0,X0,X0,X1) != X2) )),
% 0.20/0.50    inference(definition_unfolding,[],[f20,f27])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.20/0.50    inference(definition_unfolding,[],[f15,f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.20/0.50    inference(definition_unfolding,[],[f16,f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.50  % (6464)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 0.20/0.50    inference(cnf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 0.20/0.50  fof(f77,plain,(
% 0.20/0.50    r2_hidden(k1_mcart_1(sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK2)) | ~spl5_5),
% 0.20/0.50    inference(avatar_component_clause,[],[f75])).
% 0.20/0.50  fof(f75,plain,(
% 0.20/0.50    spl5_5 <=> r2_hidden(k1_mcart_1(sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.50  fof(f72,plain,(
% 0.20/0.50    sK2 != k1_mcart_1(sK0) | spl5_4),
% 0.20/0.50    inference(avatar_component_clause,[],[f70])).
% 0.20/0.50  fof(f70,plain,(
% 0.20/0.50    spl5_4 <=> sK2 = k1_mcart_1(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.50  fof(f50,plain,(
% 0.20/0.50    sK1 != k1_mcart_1(sK0) | spl5_2),
% 0.20/0.50    inference(avatar_component_clause,[],[f48])).
% 0.20/0.50  fof(f48,plain,(
% 0.20/0.50    spl5_2 <=> sK1 = k1_mcart_1(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.50  fof(f78,plain,(
% 0.20/0.50    spl5_5 | ~spl5_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f59,f53,f75])).
% 0.20/0.50  fof(f53,plain,(
% 0.20/0.50    spl5_3 <=> r2_hidden(sK0,k2_zfmisc_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.50  fof(f59,plain,(
% 0.20/0.50    r2_hidden(k1_mcart_1(sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK2)) | ~spl5_3),
% 0.20/0.50    inference(resolution,[],[f55,f36])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,k3_enumset1(X2,X2,X2,X2,X3))) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 0.20/0.50    inference(definition_unfolding,[],[f25,f27])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,plain,(
% 0.20/0.50    ! [X0,X1,X2,X3] : (((k2_mcart_1(X0) = X3 | k2_mcart_1(X0) = X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))) => ((k2_mcart_1(X0) = X3 | k2_mcart_1(X0) = X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_mcart_1)).
% 0.20/0.50  fof(f55,plain,(
% 0.20/0.50    r2_hidden(sK0,k2_zfmisc_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3))) | ~spl5_3),
% 0.20/0.50    inference(avatar_component_clause,[],[f53])).
% 0.20/0.50  fof(f73,plain,(
% 0.20/0.50    ~spl5_1 | ~spl5_4),
% 0.20/0.50    inference(avatar_split_clause,[],[f12,f70,f44])).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    spl5_1 <=> sK3 = k2_mcart_1(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.50  fof(f12,plain,(
% 0.20/0.50    sK2 != k1_mcart_1(sK0) | sK3 != k2_mcart_1(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,plain,(
% 0.20/0.50    ? [X0,X1,X2,X3] : ((k2_mcart_1(X0) != X3 | (k1_mcart_1(X0) != X2 & k1_mcart_1(X0) != X1)) & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))))),
% 0.20/0.50    inference(ennf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,negated_conjecture,(
% 0.20/0.50    ~! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))) => (k2_mcart_1(X0) = X3 & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)))),
% 0.20/0.50    inference(negated_conjecture,[],[f7])).
% 0.20/0.50  fof(f7,conjecture,(
% 0.20/0.50    ! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))) => (k2_mcart_1(X0) = X3 & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_mcart_1)).
% 0.20/0.50  fof(f68,plain,(
% 0.20/0.50    spl5_1 | ~spl5_3),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f57])).
% 0.20/0.50  fof(f57,plain,(
% 0.20/0.50    $false | (spl5_1 | ~spl5_3)),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f46,f46,f55,f37])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,k3_enumset1(X2,X2,X2,X2,X3))) | k2_mcart_1(X0) = X2 | k2_mcart_1(X0) = X3) )),
% 0.20/0.50    inference(definition_unfolding,[],[f24,f27])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))) | k2_mcart_1(X0) = X2 | k2_mcart_1(X0) = X3) )),
% 0.20/0.50    inference(cnf_transformation,[],[f10])).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    sK3 != k2_mcart_1(sK0) | spl5_1),
% 0.20/0.50    inference(avatar_component_clause,[],[f44])).
% 0.20/0.50  fof(f56,plain,(
% 0.20/0.50    spl5_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f29,f53])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    r2_hidden(sK0,k2_zfmisc_1(k3_enumset1(sK1,sK1,sK1,sK1,sK2),k3_enumset1(sK3,sK3,sK3,sK3,sK3)))),
% 0.20/0.50    inference(definition_unfolding,[],[f13,f27,f28])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 0.20/0.50    inference(definition_unfolding,[],[f14,f27])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k1_tarski(sK3)))),
% 0.20/0.50    inference(cnf_transformation,[],[f9])).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    ~spl5_1 | ~spl5_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f11,f48,f44])).
% 0.20/0.50  fof(f11,plain,(
% 0.20/0.50    sK1 != k1_mcart_1(sK0) | sK3 != k2_mcart_1(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f9])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (6491)------------------------------
% 0.20/0.50  % (6491)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (6491)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (6491)Memory used [KB]: 10746
% 0.20/0.50  % (6491)Time elapsed: 0.106 s
% 0.20/0.50  % (6491)------------------------------
% 0.20/0.50  % (6491)------------------------------
% 0.20/0.50  % (6462)Success in time 0.148 s
%------------------------------------------------------------------------------
