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
% DateTime   : Thu Dec  3 12:58:22 EST 2020

% Result     : Theorem 1.41s
% Output     : Refutation 1.41s
% Verified   : 
% Statistics : Number of formulae       :   45 (  73 expanded)
%              Number of leaves         :   10 (  23 expanded)
%              Depth                    :   13
%              Number of atoms          :  211 ( 304 expanded)
%              Number of equality atoms :  137 ( 180 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f112,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f84,f89,f95,f111])).

fof(f111,plain,
    ( spl6_2
    | spl6_3 ),
    inference(avatar_contradiction_clause,[],[f110])).

fof(f110,plain,
    ( $false
    | spl6_2
    | spl6_3 ),
    inference(subsumption_resolution,[],[f109,f83])).

fof(f83,plain,
    ( sK3 != k2_mcart_1(sK0)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl6_2
  <=> sK3 = k2_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

% (23809)Refutation not found, incomplete strategy% (23809)------------------------------
% (23809)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (23809)Termination reason: Refutation not found, incomplete strategy

% (23809)Memory used [KB]: 1663
% (23809)Time elapsed: 0.128 s
% (23809)------------------------------
% (23809)------------------------------
fof(f109,plain,
    ( sK3 = k2_mcart_1(sK0)
    | spl6_3 ),
    inference(subsumption_resolution,[],[f108,f88])).

fof(f88,plain,
    ( sK2 != k2_mcart_1(sK0)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl6_3
  <=> sK2 = k2_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f108,plain,
    ( sK2 = k2_mcart_1(sK0)
    | sK3 = k2_mcart_1(sK0) ),
    inference(duplicate_literal_removal,[],[f105])).

fof(f105,plain,
    ( sK2 = k2_mcart_1(sK0)
    | sK2 = k2_mcart_1(sK0)
    | sK2 = k2_mcart_1(sK0)
    | sK3 = k2_mcart_1(sK0) ),
    inference(resolution,[],[f91,f75])).

fof(f75,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( ~ r2_hidden(X6,k2_enumset1(X0,X1,X2,X3))
      | X2 = X6
      | X1 = X6
      | X0 = X6
      | X3 = X6 ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( X3 = X6
      | X2 = X6
      | X1 = X6
      | X0 = X6
      | ~ r2_hidden(X6,X4)
      | k2_enumset1(X0,X1,X2,X3) != X4 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_enumset1(X0,X1,X2,X3) = X4
        | ( ( ( sK5(X0,X1,X2,X3,X4) != X3
              & sK5(X0,X1,X2,X3,X4) != X2
              & sK5(X0,X1,X2,X3,X4) != X1
              & sK5(X0,X1,X2,X3,X4) != X0 )
            | ~ r2_hidden(sK5(X0,X1,X2,X3,X4),X4) )
          & ( sK5(X0,X1,X2,X3,X4) = X3
            | sK5(X0,X1,X2,X3,X4) = X2
            | sK5(X0,X1,X2,X3,X4) = X1
            | sK5(X0,X1,X2,X3,X4) = X0
            | r2_hidden(sK5(X0,X1,X2,X3,X4),X4) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X4)
              | ( X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 ) )
            & ( X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | ~ r2_hidden(X6,X4) ) )
        | k2_enumset1(X0,X1,X2,X3) != X4 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f27,f28])).

fof(f28,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( ( ( X3 != X5
              & X2 != X5
              & X1 != X5
              & X0 != X5 )
            | ~ r2_hidden(X5,X4) )
          & ( X3 = X5
            | X2 = X5
            | X1 = X5
            | X0 = X5
            | r2_hidden(X5,X4) ) )
     => ( ( ( sK5(X0,X1,X2,X3,X4) != X3
            & sK5(X0,X1,X2,X3,X4) != X2
            & sK5(X0,X1,X2,X3,X4) != X1
            & sK5(X0,X1,X2,X3,X4) != X0 )
          | ~ r2_hidden(sK5(X0,X1,X2,X3,X4),X4) )
        & ( sK5(X0,X1,X2,X3,X4) = X3
          | sK5(X0,X1,X2,X3,X4) = X2
          | sK5(X0,X1,X2,X3,X4) = X1
          | sK5(X0,X1,X2,X3,X4) = X0
          | r2_hidden(sK5(X0,X1,X2,X3,X4),X4) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_enumset1(X0,X1,X2,X3) = X4
        | ? [X5] :
            ( ( ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 )
              | ~ r2_hidden(X5,X4) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X4)
              | ( X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 ) )
            & ( X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | ~ r2_hidden(X6,X4) ) )
        | k2_enumset1(X0,X1,X2,X3) != X4 ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_enumset1(X0,X1,X2,X3) = X4
        | ? [X5] :
            ( ( ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 )
              | ~ r2_hidden(X5,X4) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X4)
              | ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X4) ) )
        | k2_enumset1(X0,X1,X2,X3) != X4 ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_enumset1(X0,X1,X2,X3) = X4
        | ? [X5] :
            ( ( ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 )
              | ~ r2_hidden(X5,X4) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X4)
              | ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X4) ) )
        | k2_enumset1(X0,X1,X2,X3) != X4 ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ( X3 = X5
            | X2 = X5
            | X1 = X5
            | X0 = X5 ) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X3 != X5
              & X2 != X5
              & X1 != X5
              & X0 != X5 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_enumset1)).

fof(f91,plain,(
    r2_hidden(k2_mcart_1(sK0),k2_enumset1(sK2,sK2,sK2,sK3)) ),
    inference(resolution,[],[f59,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f59,plain,(
    r2_hidden(sK0,k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK3))) ),
    inference(definition_unfolding,[],[f30,f57])).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f34,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f34,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f30,plain,(
    r2_hidden(sK0,k2_zfmisc_1(sK1,k2_tarski(sK2,sK3))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ( ( sK3 != k2_mcart_1(sK0)
        & sK2 != k2_mcart_1(sK0) )
      | ~ r2_hidden(k1_mcart_1(sK0),sK1) )
    & r2_hidden(sK0,k2_zfmisc_1(sK1,k2_tarski(sK2,sK3))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ( k2_mcart_1(X0) != X3
            & k2_mcart_1(X0) != X2 )
          | ~ r2_hidden(k1_mcart_1(X0),X1) )
        & r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))) )
   => ( ( ( sK3 != k2_mcart_1(sK0)
          & sK2 != k2_mcart_1(sK0) )
        | ~ r2_hidden(k1_mcart_1(sK0),sK1) )
      & r2_hidden(sK0,k2_zfmisc_1(sK1,k2_tarski(sK2,sK3))) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ( k2_mcart_1(X0) != X3
          & k2_mcart_1(X0) != X2 )
        | ~ r2_hidden(k1_mcart_1(X0),X1) )
      & r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3)))
       => ( ( k2_mcart_1(X0) = X3
            | k2_mcart_1(X0) = X2 )
          & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3)))
     => ( ( k2_mcart_1(X0) = X3
          | k2_mcart_1(X0) = X2 )
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_mcart_1)).

fof(f95,plain,(
    spl6_1 ),
    inference(avatar_contradiction_clause,[],[f94])).

fof(f94,plain,
    ( $false
    | spl6_1 ),
    inference(subsumption_resolution,[],[f90,f79])).

fof(f79,plain,
    ( ~ r2_hidden(k1_mcart_1(sK0),sK1)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl6_1
  <=> r2_hidden(k1_mcart_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f90,plain,(
    r2_hidden(k1_mcart_1(sK0),sK1) ),
    inference(resolution,[],[f59,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f89,plain,
    ( ~ spl6_1
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f31,f86,f77])).

fof(f31,plain,
    ( sK2 != k2_mcart_1(sK0)
    | ~ r2_hidden(k1_mcart_1(sK0),sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f84,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f32,f81,f77])).

fof(f32,plain,
    ( sK3 != k2_mcart_1(sK0)
    | ~ r2_hidden(k1_mcart_1(sK0),sK1) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:01:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.52  % (23817)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.53  % (23833)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.41/0.54  % (23825)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.41/0.54  % (23810)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.41/0.54  % (23809)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.41/0.54  % (23817)Refutation found. Thanks to Tanya!
% 1.41/0.54  % SZS status Theorem for theBenchmark
% 1.41/0.54  % SZS output start Proof for theBenchmark
% 1.41/0.54  fof(f112,plain,(
% 1.41/0.54    $false),
% 1.41/0.54    inference(avatar_sat_refutation,[],[f84,f89,f95,f111])).
% 1.41/0.54  fof(f111,plain,(
% 1.41/0.54    spl6_2 | spl6_3),
% 1.41/0.54    inference(avatar_contradiction_clause,[],[f110])).
% 1.41/0.54  fof(f110,plain,(
% 1.41/0.54    $false | (spl6_2 | spl6_3)),
% 1.41/0.54    inference(subsumption_resolution,[],[f109,f83])).
% 1.41/0.54  fof(f83,plain,(
% 1.41/0.54    sK3 != k2_mcart_1(sK0) | spl6_2),
% 1.41/0.54    inference(avatar_component_clause,[],[f81])).
% 1.41/0.54  fof(f81,plain,(
% 1.41/0.54    spl6_2 <=> sK3 = k2_mcart_1(sK0)),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.41/0.54  % (23809)Refutation not found, incomplete strategy% (23809)------------------------------
% 1.41/0.54  % (23809)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.54  % (23809)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.54  
% 1.41/0.54  % (23809)Memory used [KB]: 1663
% 1.41/0.54  % (23809)Time elapsed: 0.128 s
% 1.41/0.54  % (23809)------------------------------
% 1.41/0.54  % (23809)------------------------------
% 1.41/0.54  fof(f109,plain,(
% 1.41/0.54    sK3 = k2_mcart_1(sK0) | spl6_3),
% 1.41/0.54    inference(subsumption_resolution,[],[f108,f88])).
% 1.41/0.54  fof(f88,plain,(
% 1.41/0.54    sK2 != k2_mcart_1(sK0) | spl6_3),
% 1.41/0.54    inference(avatar_component_clause,[],[f86])).
% 1.41/0.54  fof(f86,plain,(
% 1.41/0.54    spl6_3 <=> sK2 = k2_mcart_1(sK0)),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.41/0.54  fof(f108,plain,(
% 1.41/0.54    sK2 = k2_mcart_1(sK0) | sK3 = k2_mcart_1(sK0)),
% 1.41/0.54    inference(duplicate_literal_removal,[],[f105])).
% 1.41/0.54  fof(f105,plain,(
% 1.41/0.54    sK2 = k2_mcart_1(sK0) | sK2 = k2_mcart_1(sK0) | sK2 = k2_mcart_1(sK0) | sK3 = k2_mcart_1(sK0)),
% 1.41/0.54    inference(resolution,[],[f91,f75])).
% 1.41/0.54  fof(f75,plain,(
% 1.41/0.54    ( ! [X6,X2,X0,X3,X1] : (~r2_hidden(X6,k2_enumset1(X0,X1,X2,X3)) | X2 = X6 | X1 = X6 | X0 = X6 | X3 = X6) )),
% 1.41/0.54    inference(equality_resolution,[],[f47])).
% 1.41/0.54  fof(f47,plain,(
% 1.41/0.54    ( ! [X6,X4,X2,X0,X3,X1] : (X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | ~r2_hidden(X6,X4) | k2_enumset1(X0,X1,X2,X3) != X4) )),
% 1.41/0.54    inference(cnf_transformation,[],[f29])).
% 1.41/0.54  fof(f29,plain,(
% 1.41/0.54    ! [X0,X1,X2,X3,X4] : ((k2_enumset1(X0,X1,X2,X3) = X4 | (((sK5(X0,X1,X2,X3,X4) != X3 & sK5(X0,X1,X2,X3,X4) != X2 & sK5(X0,X1,X2,X3,X4) != X1 & sK5(X0,X1,X2,X3,X4) != X0) | ~r2_hidden(sK5(X0,X1,X2,X3,X4),X4)) & (sK5(X0,X1,X2,X3,X4) = X3 | sK5(X0,X1,X2,X3,X4) = X2 | sK5(X0,X1,X2,X3,X4) = X1 | sK5(X0,X1,X2,X3,X4) = X0 | r2_hidden(sK5(X0,X1,X2,X3,X4),X4)))) & (! [X6] : ((r2_hidden(X6,X4) | (X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)) & (X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | ~r2_hidden(X6,X4))) | k2_enumset1(X0,X1,X2,X3) != X4))),
% 1.41/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f27,f28])).
% 1.41/0.54  fof(f28,plain,(
% 1.41/0.54    ! [X4,X3,X2,X1,X0] : (? [X5] : (((X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5) | ~r2_hidden(X5,X4)) & (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5 | r2_hidden(X5,X4))) => (((sK5(X0,X1,X2,X3,X4) != X3 & sK5(X0,X1,X2,X3,X4) != X2 & sK5(X0,X1,X2,X3,X4) != X1 & sK5(X0,X1,X2,X3,X4) != X0) | ~r2_hidden(sK5(X0,X1,X2,X3,X4),X4)) & (sK5(X0,X1,X2,X3,X4) = X3 | sK5(X0,X1,X2,X3,X4) = X2 | sK5(X0,X1,X2,X3,X4) = X1 | sK5(X0,X1,X2,X3,X4) = X0 | r2_hidden(sK5(X0,X1,X2,X3,X4),X4))))),
% 1.41/0.54    introduced(choice_axiom,[])).
% 1.41/0.54  fof(f27,plain,(
% 1.41/0.54    ! [X0,X1,X2,X3,X4] : ((k2_enumset1(X0,X1,X2,X3) = X4 | ? [X5] : (((X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5) | ~r2_hidden(X5,X4)) & (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5 | r2_hidden(X5,X4)))) & (! [X6] : ((r2_hidden(X6,X4) | (X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)) & (X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | ~r2_hidden(X6,X4))) | k2_enumset1(X0,X1,X2,X3) != X4))),
% 1.41/0.54    inference(rectify,[],[f26])).
% 1.41/0.54  fof(f26,plain,(
% 1.41/0.54    ! [X0,X1,X2,X3,X4] : ((k2_enumset1(X0,X1,X2,X3) = X4 | ? [X5] : (((X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5) | ~r2_hidden(X5,X4)) & (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5 | r2_hidden(X5,X4)))) & (! [X5] : ((r2_hidden(X5,X4) | (X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)) & (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X4))) | k2_enumset1(X0,X1,X2,X3) != X4))),
% 1.41/0.54    inference(flattening,[],[f25])).
% 1.41/0.54  fof(f25,plain,(
% 1.41/0.54    ! [X0,X1,X2,X3,X4] : ((k2_enumset1(X0,X1,X2,X3) = X4 | ? [X5] : (((X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5) | ~r2_hidden(X5,X4)) & ((X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5) | r2_hidden(X5,X4)))) & (! [X5] : ((r2_hidden(X5,X4) | (X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)) & ((X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5) | ~r2_hidden(X5,X4))) | k2_enumset1(X0,X1,X2,X3) != X4))),
% 1.41/0.54    inference(nnf_transformation,[],[f14])).
% 1.41/0.54  fof(f14,plain,(
% 1.41/0.54    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> ! [X5] : (r2_hidden(X5,X4) <=> (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5)))),
% 1.41/0.54    inference(ennf_transformation,[],[f7])).
% 1.41/0.54  fof(f7,axiom,(
% 1.41/0.54    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> ! [X5] : (r2_hidden(X5,X4) <=> ~(X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)))),
% 1.41/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_enumset1)).
% 1.41/0.54  fof(f91,plain,(
% 1.41/0.54    r2_hidden(k2_mcart_1(sK0),k2_enumset1(sK2,sK2,sK2,sK3))),
% 1.41/0.54    inference(resolution,[],[f59,f40])).
% 1.41/0.54  fof(f40,plain,(
% 1.41/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f13])).
% 1.41/0.54  fof(f13,plain,(
% 1.41/0.54    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.41/0.54    inference(ennf_transformation,[],[f8])).
% 1.41/0.54  fof(f8,axiom,(
% 1.41/0.54    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 1.41/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 1.41/0.54  fof(f59,plain,(
% 1.41/0.54    r2_hidden(sK0,k2_zfmisc_1(sK1,k2_enumset1(sK2,sK2,sK2,sK3)))),
% 1.41/0.54    inference(definition_unfolding,[],[f30,f57])).
% 1.41/0.54  fof(f57,plain,(
% 1.41/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.41/0.54    inference(definition_unfolding,[],[f34,f38])).
% 1.41/0.54  fof(f38,plain,(
% 1.41/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f4])).
% 1.41/0.54  fof(f4,axiom,(
% 1.41/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.41/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.41/0.54  fof(f34,plain,(
% 1.41/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f3])).
% 1.41/0.54  fof(f3,axiom,(
% 1.41/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.41/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.41/0.54  fof(f30,plain,(
% 1.41/0.54    r2_hidden(sK0,k2_zfmisc_1(sK1,k2_tarski(sK2,sK3)))),
% 1.41/0.54    inference(cnf_transformation,[],[f16])).
% 1.41/0.54  fof(f16,plain,(
% 1.41/0.54    ((sK3 != k2_mcart_1(sK0) & sK2 != k2_mcart_1(sK0)) | ~r2_hidden(k1_mcart_1(sK0),sK1)) & r2_hidden(sK0,k2_zfmisc_1(sK1,k2_tarski(sK2,sK3)))),
% 1.41/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f15])).
% 1.41/0.54  fof(f15,plain,(
% 1.41/0.54    ? [X0,X1,X2,X3] : (((k2_mcart_1(X0) != X3 & k2_mcart_1(X0) != X2) | ~r2_hidden(k1_mcart_1(X0),X1)) & r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3)))) => (((sK3 != k2_mcart_1(sK0) & sK2 != k2_mcart_1(sK0)) | ~r2_hidden(k1_mcart_1(sK0),sK1)) & r2_hidden(sK0,k2_zfmisc_1(sK1,k2_tarski(sK2,sK3))))),
% 1.41/0.54    introduced(choice_axiom,[])).
% 1.41/0.54  fof(f11,plain,(
% 1.41/0.54    ? [X0,X1,X2,X3] : (((k2_mcart_1(X0) != X3 & k2_mcart_1(X0) != X2) | ~r2_hidden(k1_mcart_1(X0),X1)) & r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))))),
% 1.41/0.54    inference(ennf_transformation,[],[f10])).
% 1.41/0.54  fof(f10,negated_conjecture,(
% 1.41/0.54    ~! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))) => ((k2_mcart_1(X0) = X3 | k2_mcart_1(X0) = X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 1.41/0.54    inference(negated_conjecture,[],[f9])).
% 1.41/0.54  fof(f9,conjecture,(
% 1.41/0.54    ! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))) => ((k2_mcart_1(X0) = X3 | k2_mcart_1(X0) = X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 1.41/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_mcart_1)).
% 1.41/0.54  fof(f95,plain,(
% 1.41/0.54    spl6_1),
% 1.41/0.54    inference(avatar_contradiction_clause,[],[f94])).
% 1.41/0.54  fof(f94,plain,(
% 1.41/0.54    $false | spl6_1),
% 1.41/0.54    inference(subsumption_resolution,[],[f90,f79])).
% 1.41/0.54  fof(f79,plain,(
% 1.41/0.54    ~r2_hidden(k1_mcart_1(sK0),sK1) | spl6_1),
% 1.41/0.54    inference(avatar_component_clause,[],[f77])).
% 1.41/0.54  fof(f77,plain,(
% 1.41/0.54    spl6_1 <=> r2_hidden(k1_mcart_1(sK0),sK1)),
% 1.41/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.41/0.54  fof(f90,plain,(
% 1.41/0.54    r2_hidden(k1_mcart_1(sK0),sK1)),
% 1.41/0.54    inference(resolution,[],[f59,f39])).
% 1.41/0.54  fof(f39,plain,(
% 1.41/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f13])).
% 1.41/0.54  fof(f89,plain,(
% 1.41/0.54    ~spl6_1 | ~spl6_3),
% 1.41/0.54    inference(avatar_split_clause,[],[f31,f86,f77])).
% 1.41/0.54  fof(f31,plain,(
% 1.41/0.54    sK2 != k2_mcart_1(sK0) | ~r2_hidden(k1_mcart_1(sK0),sK1)),
% 1.41/0.54    inference(cnf_transformation,[],[f16])).
% 1.41/0.54  fof(f84,plain,(
% 1.41/0.54    ~spl6_1 | ~spl6_2),
% 1.41/0.54    inference(avatar_split_clause,[],[f32,f81,f77])).
% 1.41/0.54  fof(f32,plain,(
% 1.41/0.54    sK3 != k2_mcart_1(sK0) | ~r2_hidden(k1_mcart_1(sK0),sK1)),
% 1.41/0.54    inference(cnf_transformation,[],[f16])).
% 1.41/0.54  % SZS output end Proof for theBenchmark
% 1.41/0.54  % (23817)------------------------------
% 1.41/0.54  % (23817)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.54  % (23817)Termination reason: Refutation
% 1.41/0.54  
% 1.41/0.54  % (23817)Memory used [KB]: 10746
% 1.41/0.54  % (23817)Time elapsed: 0.123 s
% 1.41/0.54  % (23817)------------------------------
% 1.41/0.54  % (23817)------------------------------
% 1.41/0.54  % (23808)Success in time 0.19 s
%------------------------------------------------------------------------------
