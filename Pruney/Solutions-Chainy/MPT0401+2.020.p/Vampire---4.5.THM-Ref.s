%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:16 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 129 expanded)
%              Number of leaves         :   24 (  55 expanded)
%              Depth                    :    9
%              Number of atoms          :  179 ( 295 expanded)
%              Number of equality atoms :   22 (  41 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f135,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f50,f54,f58,f62,f69,f73,f78,f84,f99,f131,f134])).

fof(f134,plain,
    ( spl3_2
    | ~ spl3_6
    | ~ spl3_18 ),
    inference(avatar_contradiction_clause,[],[f133])).

fof(f133,plain,
    ( $false
    | spl3_2
    | ~ spl3_6
    | ~ spl3_18 ),
    inference(subsumption_resolution,[],[f132,f49])).

fof(f49,plain,
    ( ~ r1_tarski(sK2,sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl3_2
  <=> r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f132,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl3_6
    | ~ spl3_18 ),
    inference(resolution,[],[f130,f68])).

fof(f68,plain,
    ( r1_setfam_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl3_6
  <=> r1_setfam_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f130,plain,
    ( ! [X0] :
        ( ~ r1_setfam_1(sK1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
        | r1_tarski(sK2,X0) )
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl3_18
  <=> ! [X0] :
        ( r1_tarski(sK2,X0)
        | ~ r1_setfam_1(sK1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f131,plain,
    ( spl3_18
    | ~ spl3_9
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f124,f97,f82,f129])).

fof(f82,plain,
    ( spl3_9
  <=> ! [X0] :
        ( r1_tarski(sK2,k3_tarski(X0))
        | ~ r1_setfam_1(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f97,plain,
    ( spl3_12
  <=> ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f124,plain,
    ( ! [X0] :
        ( r1_tarski(sK2,X0)
        | ~ r1_setfam_1(sK1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )
    | ~ spl3_9
    | ~ spl3_12 ),
    inference(superposition,[],[f83,f98])).

fof(f98,plain,
    ( ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f97])).

fof(f83,plain,
    ( ! [X0] :
        ( r1_tarski(sK2,k3_tarski(X0))
        | ~ r1_setfam_1(sK1,X0) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f82])).

fof(f99,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f40,f97])).

fof(f40,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f24,f38])).

fof(f38,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f25,f37])).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f26,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f29,f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f31,f34])).

fof(f34,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f32,f33])).

fof(f33,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_enumset1)).

fof(f32,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f31,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f29,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f26,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f25,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f24,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).

fof(f84,plain,
    ( spl3_9
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f79,f76,f56,f82])).

fof(f56,plain,
    ( spl3_4
  <=> ! [X1,X0] :
        ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
        | ~ r1_setfam_1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f76,plain,
    ( spl3_8
  <=> ! [X0] :
        ( r1_tarski(sK2,X0)
        | ~ r1_tarski(k3_tarski(sK1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f79,plain,
    ( ! [X0] :
        ( r1_tarski(sK2,k3_tarski(X0))
        | ~ r1_setfam_1(sK1,X0) )
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(resolution,[],[f77,f57])).

fof(f57,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
        | ~ r1_setfam_1(X0,X1) )
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f56])).

fof(f77,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k3_tarski(sK1),X0)
        | r1_tarski(sK2,X0) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f76])).

% (17333)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
fof(f78,plain,
    ( spl3_8
    | ~ spl3_1
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f74,f71,f42,f76])).

fof(f42,plain,
    ( spl3_1
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f71,plain,
    ( spl3_7
  <=> ! [X1,X0,X2] :
        ( ~ r1_tarski(k3_tarski(X0),X1)
        | r1_tarski(X2,X1)
        | ~ r2_hidden(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f74,plain,
    ( ! [X0] :
        ( r1_tarski(sK2,X0)
        | ~ r1_tarski(k3_tarski(sK1),X0) )
    | ~ spl3_1
    | ~ spl3_7 ),
    inference(resolution,[],[f72,f44])).

fof(f44,plain,
    ( r2_hidden(sK2,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f72,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X2,X0)
        | r1_tarski(X2,X1)
        | ~ r1_tarski(k3_tarski(X0),X1) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f71])).

fof(f73,plain,
    ( spl3_7
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f63,f60,f52,f71])).

fof(f52,plain,
    ( spl3_3
  <=> ! [X1,X0] :
        ( r1_tarski(X0,k3_tarski(X1))
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f60,plain,
    ( spl3_5
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,X2)
        | ~ r1_tarski(X1,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f63,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k3_tarski(X0),X1)
        | r1_tarski(X2,X1)
        | ~ r2_hidden(X2,X0) )
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(resolution,[],[f61,f53])).

fof(f53,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,k3_tarski(X1))
        | ~ r2_hidden(X0,X1) )
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f52])).

% (17346)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
fof(f61,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_tarski(X1,X2)
        | r1_tarski(X0,X2) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f60])).

fof(f69,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f39,f66])).

fof(f39,plain,(
    r1_setfam_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(definition_unfolding,[],[f21,f38])).

fof(f21,plain,(
    r1_setfam_1(sK1,k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ~ r1_tarski(sK2,sK0)
    & r2_hidden(sK2,sK1)
    & r1_setfam_1(sK1,k1_tarski(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f19,f18])).

fof(f18,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(X2,X0)
            & r2_hidden(X2,X1) )
        & r1_setfam_1(X1,k1_tarski(X0)) )
   => ( ? [X2] :
          ( ~ r1_tarski(X2,sK0)
          & r2_hidden(X2,sK1) )
      & r1_setfam_1(sK1,k1_tarski(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X2] :
        ( ~ r1_tarski(X2,sK0)
        & r2_hidden(X2,sK1) )
   => ( ~ r1_tarski(sK2,sK0)
      & r2_hidden(sK2,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,X0)
          & r2_hidden(X2,X1) )
      & r1_setfam_1(X1,k1_tarski(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_setfam_1(X1,k1_tarski(X0))
       => ! [X2] :
            ( r2_hidden(X2,X1)
           => r1_tarski(X2,X0) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( r1_setfam_1(X1,k1_tarski(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_setfam_1)).

fof(f62,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f30,f60])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f58,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f28,f56])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_setfam_1)).

fof(f54,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f27,f52])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_zfmisc_1)).

fof(f50,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f23,f47])).

fof(f23,plain,(
    ~ r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f45,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f22,f42])).

fof(f22,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:50:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (17338)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.46  % (17336)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.46  % (17338)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f135,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f45,f50,f54,f58,f62,f69,f73,f78,f84,f99,f131,f134])).
% 0.21/0.46  fof(f134,plain,(
% 0.21/0.46    spl3_2 | ~spl3_6 | ~spl3_18),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f133])).
% 0.21/0.46  fof(f133,plain,(
% 0.21/0.46    $false | (spl3_2 | ~spl3_6 | ~spl3_18)),
% 0.21/0.46    inference(subsumption_resolution,[],[f132,f49])).
% 0.21/0.46  fof(f49,plain,(
% 0.21/0.46    ~r1_tarski(sK2,sK0) | spl3_2),
% 0.21/0.46    inference(avatar_component_clause,[],[f47])).
% 0.21/0.46  fof(f47,plain,(
% 0.21/0.46    spl3_2 <=> r1_tarski(sK2,sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.46  fof(f132,plain,(
% 0.21/0.46    r1_tarski(sK2,sK0) | (~spl3_6 | ~spl3_18)),
% 0.21/0.46    inference(resolution,[],[f130,f68])).
% 0.21/0.46  fof(f68,plain,(
% 0.21/0.46    r1_setfam_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~spl3_6),
% 0.21/0.46    inference(avatar_component_clause,[],[f66])).
% 0.21/0.46  fof(f66,plain,(
% 0.21/0.46    spl3_6 <=> r1_setfam_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.46  fof(f130,plain,(
% 0.21/0.46    ( ! [X0] : (~r1_setfam_1(sK1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) | r1_tarski(sK2,X0)) ) | ~spl3_18),
% 0.21/0.46    inference(avatar_component_clause,[],[f129])).
% 0.21/0.46  fof(f129,plain,(
% 0.21/0.46    spl3_18 <=> ! [X0] : (r1_tarski(sK2,X0) | ~r1_setfam_1(sK1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.46  fof(f131,plain,(
% 0.21/0.46    spl3_18 | ~spl3_9 | ~spl3_12),
% 0.21/0.46    inference(avatar_split_clause,[],[f124,f97,f82,f129])).
% 0.21/0.46  fof(f82,plain,(
% 0.21/0.46    spl3_9 <=> ! [X0] : (r1_tarski(sK2,k3_tarski(X0)) | ~r1_setfam_1(sK1,X0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.46  fof(f97,plain,(
% 0.21/0.46    spl3_12 <=> ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.46  fof(f124,plain,(
% 0.21/0.46    ( ! [X0] : (r1_tarski(sK2,X0) | ~r1_setfam_1(sK1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) ) | (~spl3_9 | ~spl3_12)),
% 0.21/0.46    inference(superposition,[],[f83,f98])).
% 0.21/0.46  fof(f98,plain,(
% 0.21/0.46    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) ) | ~spl3_12),
% 0.21/0.46    inference(avatar_component_clause,[],[f97])).
% 0.21/0.46  fof(f83,plain,(
% 0.21/0.46    ( ! [X0] : (r1_tarski(sK2,k3_tarski(X0)) | ~r1_setfam_1(sK1,X0)) ) | ~spl3_9),
% 0.21/0.46    inference(avatar_component_clause,[],[f82])).
% 0.21/0.46  fof(f99,plain,(
% 0.21/0.46    spl3_12),
% 0.21/0.46    inference(avatar_split_clause,[],[f40,f97])).
% 0.21/0.46  fof(f40,plain,(
% 0.21/0.46    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 0.21/0.46    inference(definition_unfolding,[],[f24,f38])).
% 0.21/0.46  fof(f38,plain,(
% 0.21/0.46    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.21/0.46    inference(definition_unfolding,[],[f25,f37])).
% 0.21/0.46  fof(f37,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.21/0.46    inference(definition_unfolding,[],[f26,f36])).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.21/0.46    inference(definition_unfolding,[],[f29,f35])).
% 0.21/0.46  fof(f35,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.21/0.46    inference(definition_unfolding,[],[f31,f34])).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.21/0.46    inference(definition_unfolding,[],[f32,f33])).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    ( ! [X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f7])).
% 0.21/0.46  fof(f7,axiom,(
% 0.21/0.46    ! [X0,X1,X2,X3,X4,X5] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_enumset1)).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,axiom,(
% 0.21/0.46    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = X0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f8])).
% 0.21/0.46  fof(f8,axiom,(
% 0.21/0.46    ! [X0] : k3_tarski(k1_tarski(X0)) = X0),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).
% 0.21/0.46  fof(f84,plain,(
% 0.21/0.46    spl3_9 | ~spl3_4 | ~spl3_8),
% 0.21/0.46    inference(avatar_split_clause,[],[f79,f76,f56,f82])).
% 0.21/0.46  fof(f56,plain,(
% 0.21/0.46    spl3_4 <=> ! [X1,X0] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_setfam_1(X0,X1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.46  fof(f76,plain,(
% 0.21/0.46    spl3_8 <=> ! [X0] : (r1_tarski(sK2,X0) | ~r1_tarski(k3_tarski(sK1),X0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.46  fof(f79,plain,(
% 0.21/0.46    ( ! [X0] : (r1_tarski(sK2,k3_tarski(X0)) | ~r1_setfam_1(sK1,X0)) ) | (~spl3_4 | ~spl3_8)),
% 0.21/0.46    inference(resolution,[],[f77,f57])).
% 0.21/0.46  fof(f57,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_setfam_1(X0,X1)) ) | ~spl3_4),
% 0.21/0.46    inference(avatar_component_clause,[],[f56])).
% 0.21/0.46  fof(f77,plain,(
% 0.21/0.46    ( ! [X0] : (~r1_tarski(k3_tarski(sK1),X0) | r1_tarski(sK2,X0)) ) | ~spl3_8),
% 0.21/0.46    inference(avatar_component_clause,[],[f76])).
% 0.21/0.46  % (17333)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.46  fof(f78,plain,(
% 0.21/0.46    spl3_8 | ~spl3_1 | ~spl3_7),
% 0.21/0.46    inference(avatar_split_clause,[],[f74,f71,f42,f76])).
% 0.21/0.46  fof(f42,plain,(
% 0.21/0.46    spl3_1 <=> r2_hidden(sK2,sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.46  fof(f71,plain,(
% 0.21/0.46    spl3_7 <=> ! [X1,X0,X2] : (~r1_tarski(k3_tarski(X0),X1) | r1_tarski(X2,X1) | ~r2_hidden(X2,X0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.46  fof(f74,plain,(
% 0.21/0.46    ( ! [X0] : (r1_tarski(sK2,X0) | ~r1_tarski(k3_tarski(sK1),X0)) ) | (~spl3_1 | ~spl3_7)),
% 0.21/0.46    inference(resolution,[],[f72,f44])).
% 0.21/0.46  fof(f44,plain,(
% 0.21/0.46    r2_hidden(sK2,sK1) | ~spl3_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f42])).
% 0.21/0.46  fof(f72,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r1_tarski(X2,X1) | ~r1_tarski(k3_tarski(X0),X1)) ) | ~spl3_7),
% 0.21/0.46    inference(avatar_component_clause,[],[f71])).
% 0.21/0.46  fof(f73,plain,(
% 0.21/0.46    spl3_7 | ~spl3_3 | ~spl3_5),
% 0.21/0.46    inference(avatar_split_clause,[],[f63,f60,f52,f71])).
% 0.21/0.46  fof(f52,plain,(
% 0.21/0.46    spl3_3 <=> ! [X1,X0] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.46  fof(f60,plain,(
% 0.21/0.46    spl3_5 <=> ! [X1,X0,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.46  fof(f63,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~r1_tarski(k3_tarski(X0),X1) | r1_tarski(X2,X1) | ~r2_hidden(X2,X0)) ) | (~spl3_3 | ~spl3_5)),
% 0.21/0.46    inference(resolution,[],[f61,f53])).
% 0.21/0.46  fof(f53,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) ) | ~spl3_3),
% 0.21/0.46    inference(avatar_component_clause,[],[f52])).
% 0.21/0.46  % (17346)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.46  fof(f61,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) ) | ~spl3_5),
% 0.21/0.46    inference(avatar_component_clause,[],[f60])).
% 0.21/0.46  fof(f69,plain,(
% 0.21/0.46    spl3_6),
% 0.21/0.46    inference(avatar_split_clause,[],[f39,f66])).
% 0.21/0.46  fof(f39,plain,(
% 0.21/0.46    r1_setfam_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 0.21/0.46    inference(definition_unfolding,[],[f21,f38])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    r1_setfam_1(sK1,k1_tarski(sK0))),
% 0.21/0.46    inference(cnf_transformation,[],[f20])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    (~r1_tarski(sK2,sK0) & r2_hidden(sK2,sK1)) & r1_setfam_1(sK1,k1_tarski(sK0))),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f19,f18])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ? [X0,X1] : (? [X2] : (~r1_tarski(X2,X0) & r2_hidden(X2,X1)) & r1_setfam_1(X1,k1_tarski(X0))) => (? [X2] : (~r1_tarski(X2,sK0) & r2_hidden(X2,sK1)) & r1_setfam_1(sK1,k1_tarski(sK0)))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ? [X2] : (~r1_tarski(X2,sK0) & r2_hidden(X2,sK1)) => (~r1_tarski(sK2,sK0) & r2_hidden(sK2,sK1))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ? [X0,X1] : (? [X2] : (~r1_tarski(X2,X0) & r2_hidden(X2,X1)) & r1_setfam_1(X1,k1_tarski(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f12])).
% 0.21/0.46  fof(f12,negated_conjecture,(
% 0.21/0.46    ~! [X0,X1] : (r1_setfam_1(X1,k1_tarski(X0)) => ! [X2] : (r2_hidden(X2,X1) => r1_tarski(X2,X0)))),
% 0.21/0.46    inference(negated_conjecture,[],[f11])).
% 0.21/0.46  fof(f11,conjecture,(
% 0.21/0.46    ! [X0,X1] : (r1_setfam_1(X1,k1_tarski(X0)) => ! [X2] : (r2_hidden(X2,X1) => r1_tarski(X2,X0)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_setfam_1)).
% 0.21/0.46  fof(f62,plain,(
% 0.21/0.46    spl3_5),
% 0.21/0.46    inference(avatar_split_clause,[],[f30,f60])).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f17])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.46    inference(flattening,[],[f16])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.46    inference(ennf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.46  fof(f58,plain,(
% 0.21/0.46    spl3_4),
% 0.21/0.46    inference(avatar_split_clause,[],[f28,f56])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_setfam_1(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_setfam_1(X0,X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f10])).
% 0.21/0.46  fof(f10,axiom,(
% 0.21/0.46    ! [X0,X1] : (r1_setfam_1(X0,X1) => r1_tarski(k3_tarski(X0),k3_tarski(X1)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_setfam_1)).
% 0.21/0.46  fof(f54,plain,(
% 0.21/0.46    spl3_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f27,f52])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f14])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,axiom,(
% 0.21/0.46    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_zfmisc_1)).
% 0.21/0.46  fof(f50,plain,(
% 0.21/0.46    ~spl3_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f23,f47])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    ~r1_tarski(sK2,sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f20])).
% 0.21/0.46  fof(f45,plain,(
% 0.21/0.46    spl3_1),
% 0.21/0.46    inference(avatar_split_clause,[],[f22,f42])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    r2_hidden(sK2,sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f20])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (17338)------------------------------
% 0.21/0.46  % (17338)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (17338)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (17338)Memory used [KB]: 6140
% 0.21/0.46  % (17338)Time elapsed: 0.061 s
% 0.21/0.46  % (17338)------------------------------
% 0.21/0.46  % (17338)------------------------------
% 0.21/0.46  % (17337)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.46  % (17330)Success in time 0.108 s
%------------------------------------------------------------------------------
