%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:21 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   46 (  68 expanded)
%              Number of leaves         :   12 (  25 expanded)
%              Depth                    :    9
%              Number of atoms          :   83 ( 124 expanded)
%              Number of equality atoms :   43 (  70 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f72,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f36,f45,f67,f70,f71])).

fof(f71,plain,
    ( ~ spl5_2
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f69,f64,f38])).

fof(f38,plain,
    ( spl5_2
  <=> sK0 = k2_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f64,plain,
    ( spl5_6
  <=> sK0 = k4_tarski(sK3(sK1,sK2,sK0),sK4(sK1,sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f69,plain,
    ( sK0 != k2_mcart_1(sK0)
    | ~ spl5_6 ),
    inference(superposition,[],[f30,f66])).

fof(f66,plain,
    ( sK0 = k4_tarski(sK3(sK1,sK2,sK0),sK4(sK1,sK2,sK0))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f64])).

fof(f30,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f17])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(X1,X2) != X0
      | k2_mcart_1(X0) != X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f70,plain,
    ( ~ spl5_3
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f68,f64,f42])).

fof(f42,plain,
    ( spl5_3
  <=> sK0 = k1_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f68,plain,
    ( sK0 != k1_mcart_1(sK0)
    | ~ spl5_6 ),
    inference(superposition,[],[f31,f66])).

fof(f31,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != k1_mcart_1(k4_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f16])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(X1,X2) != X0
      | k1_mcart_1(X0) != X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f67,plain,
    ( spl5_6
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f62,f33,f64])).

fof(f33,plain,
    ( spl5_1
  <=> r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f62,plain,
    ( sK0 = k4_tarski(sK3(sK1,sK2,sK0),sK4(sK1,sK2,sK0))
    | ~ spl5_1 ),
    inference(resolution,[],[f55,f35])).

fof(f35,plain,
    ( r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | k4_tarski(sK3(X1,X2,X0),sK4(X1,X2,X0)) = X0 ) ),
    inference(resolution,[],[f25,f46])).

% (22971)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
fof(f46,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f29,f28])).

fof(f28,plain,(
    ! [X0] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f18,f27])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f20,f26])).

fof(f26,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f21,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] : k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_enumset1)).

fof(f21,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f18,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f19,f27])).

fof(f19,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | ~ r2_hidden(X3,X0)
      | k4_tarski(sK3(X1,X2,X3),sK4(X1,X2,X3)) = X3 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4,X5] :
          ( k4_tarski(X4,X5) = X3
          & r2_hidden(X5,X2)
          & r2_hidden(X4,X1) )
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ! [X4,X5] :
            ~ ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X2)
              & r2_hidden(X4,X1) )
        & r2_hidden(X3,X0)
        & r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_zfmisc_1)).

fof(f45,plain,
    ( spl5_2
    | spl5_3 ),
    inference(avatar_split_clause,[],[f14,f42,f38])).

fof(f14,plain,
    ( sK0 = k1_mcart_1(sK0)
    | sK0 = k2_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ( k2_mcart_1(X0) = X0
        | k1_mcart_1(X0) = X0 )
      & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
       => ( k2_mcart_1(X0) != X0
          & k1_mcart_1(X0) != X0 ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_mcart_1)).

fof(f36,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f15,f33])).

fof(f15,plain,(
    r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:57:04 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.20/0.49  % (22963)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.49  % (22967)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.50  % (22967)Refutation not found, incomplete strategy% (22967)------------------------------
% 0.20/0.50  % (22967)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (22967)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (22967)Memory used [KB]: 6140
% 0.20/0.50  % (22967)Time elapsed: 0.107 s
% 0.20/0.50  % (22967)------------------------------
% 0.20/0.50  % (22967)------------------------------
% 0.20/0.50  % (22964)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (22979)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.51  % (22972)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.51  % (22972)Refutation not found, incomplete strategy% (22972)------------------------------
% 0.20/0.51  % (22972)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (22979)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % (22972)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (22972)Memory used [KB]: 10618
% 0.20/0.51  % (22972)Time elapsed: 0.117 s
% 0.20/0.51  % (22972)------------------------------
% 0.20/0.51  % (22972)------------------------------
% 0.20/0.51  % (22992)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f72,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f36,f45,f67,f70,f71])).
% 0.20/0.51  fof(f71,plain,(
% 0.20/0.51    ~spl5_2 | ~spl5_6),
% 0.20/0.51    inference(avatar_split_clause,[],[f69,f64,f38])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    spl5_2 <=> sK0 = k2_mcart_1(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.51  fof(f64,plain,(
% 0.20/0.51    spl5_6 <=> sK0 = k4_tarski(sK3(sK1,sK2,sK0),sK4(sK1,sK2,sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.20/0.51  fof(f69,plain,(
% 0.20/0.51    sK0 != k2_mcart_1(sK0) | ~spl5_6),
% 0.20/0.51    inference(superposition,[],[f30,f66])).
% 0.20/0.51  fof(f66,plain,(
% 0.20/0.51    sK0 = k4_tarski(sK3(sK1,sK2,sK0),sK4(sK1,sK2,sK0)) | ~spl5_6),
% 0.20/0.51    inference(avatar_component_clause,[],[f64])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ( ! [X2,X1] : (k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2))) )),
% 0.20/0.51    inference(equality_resolution,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k4_tarski(X1,X2) != X0 | k2_mcart_1(X0) != X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    ! [X0] : ((k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0) | ! [X1,X2] : k4_tarski(X1,X2) != X0)),
% 0.20/0.51    inference(ennf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).
% 0.20/0.51  fof(f70,plain,(
% 0.20/0.51    ~spl5_3 | ~spl5_6),
% 0.20/0.51    inference(avatar_split_clause,[],[f68,f64,f42])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    spl5_3 <=> sK0 = k1_mcart_1(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.51  fof(f68,plain,(
% 0.20/0.51    sK0 != k1_mcart_1(sK0) | ~spl5_6),
% 0.20/0.51    inference(superposition,[],[f31,f66])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ( ! [X2,X1] : (k4_tarski(X1,X2) != k1_mcart_1(k4_tarski(X1,X2))) )),
% 0.20/0.51    inference(equality_resolution,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k4_tarski(X1,X2) != X0 | k1_mcart_1(X0) != X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f12])).
% 0.20/0.51  fof(f67,plain,(
% 0.20/0.51    spl5_6 | ~spl5_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f62,f33,f64])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    spl5_1 <=> r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.51  fof(f62,plain,(
% 0.20/0.51    sK0 = k4_tarski(sK3(sK1,sK2,sK0),sK4(sK1,sK2,sK0)) | ~spl5_1),
% 0.20/0.51    inference(resolution,[],[f55,f35])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) | ~spl5_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f33])).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | k4_tarski(sK3(X1,X2,X0),sK4(X1,X2,X0)) = X0) )),
% 0.20/0.51    inference(resolution,[],[f25,f46])).
% 0.20/0.51  % (22971)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.20/0.51    inference(superposition,[],[f29,f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ( ! [X0] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X0)) = X0) )),
% 0.20/0.51    inference(definition_unfolding,[],[f18,f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 0.20/0.51    inference(definition_unfolding,[],[f20,f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f21,f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_enumset1)).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,plain,(
% 0.20/0.51    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.20/0.51    inference(rectify,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 0.20/0.51    inference(definition_unfolding,[],[f19,f27])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | ~r2_hidden(X3,X0) | k4_tarski(sK3(X1,X2,X3),sK4(X1,X2,X3)) = X3) )),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X2) & r2_hidden(X4,X1)) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2)))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3] : ~(! [X4,X5] : ~(k4_tarski(X4,X5) = X3 & r2_hidden(X5,X2) & r2_hidden(X4,X1)) & r2_hidden(X3,X0) & r1_tarski(X0,k2_zfmisc_1(X1,X2)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_zfmisc_1)).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    spl5_2 | spl5_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f14,f42,f38])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    sK0 = k1_mcart_1(sK0) | sK0 = k2_mcart_1(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,plain,(
% 0.20/0.51    ? [X0,X1,X2] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.20/0.51    inference(ennf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,negated_conjecture,(
% 0.20/0.51    ~! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.20/0.51    inference(negated_conjecture,[],[f8])).
% 0.20/0.51  fof(f8,conjecture,(
% 0.20/0.51    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_mcart_1)).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    spl5_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f15,f33])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))),
% 0.20/0.51    inference(cnf_transformation,[],[f11])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (22979)------------------------------
% 0.20/0.51  % (22979)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (22979)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (22979)Memory used [KB]: 10746
% 0.20/0.51  % (22979)Time elapsed: 0.117 s
% 0.20/0.51  % (22979)------------------------------
% 0.20/0.51  % (22979)------------------------------
% 0.20/0.51  % (22968)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (22971)Refutation not found, incomplete strategy% (22971)------------------------------
% 0.20/0.51  % (22971)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (22971)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (22971)Memory used [KB]: 10618
% 0.20/0.51  % (22971)Time elapsed: 0.078 s
% 0.20/0.51  % (22971)------------------------------
% 0.20/0.51  % (22971)------------------------------
% 0.20/0.51  % (22962)Success in time 0.168 s
%------------------------------------------------------------------------------
