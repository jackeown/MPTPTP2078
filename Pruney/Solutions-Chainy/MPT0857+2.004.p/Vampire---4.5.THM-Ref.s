%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:16 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   41 (  60 expanded)
%              Number of leaves         :    9 (  18 expanded)
%              Depth                    :   11
%              Number of atoms          :  148 ( 202 expanded)
%              Number of equality atoms :   67 (  84 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f60,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f50,f59])).

fof(f59,plain,(
    spl5_2 ),
    inference(avatar_contradiction_clause,[],[f58])).

fof(f58,plain,
    ( $false
    | spl5_2 ),
    inference(subsumption_resolution,[],[f57,f42])).

fof(f42,plain,
    ( sK3 != k2_mcart_1(sK1)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl5_2
  <=> sK3 = k2_mcart_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f57,plain,(
    sK3 = k2_mcart_1(sK1) ),
    inference(duplicate_literal_removal,[],[f56])).

fof(f56,plain,
    ( sK3 = k2_mcart_1(sK1)
    | sK3 = k2_mcart_1(sK1) ),
    inference(resolution,[],[f53,f51])).

fof(f51,plain,(
    r2_hidden(k2_mcart_1(sK1),k2_tarski(sK3,sK3)) ),
    inference(resolution,[],[f22,f31])).

fof(f31,plain,(
    r2_hidden(sK1,k2_zfmisc_1(sK2,k2_tarski(sK3,sK3))) ),
    inference(definition_unfolding,[],[f18,f20])).

fof(f20,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f18,plain,(
    r2_hidden(sK1,k2_zfmisc_1(sK2,k1_tarski(sK3))) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( ( sK3 != k2_mcart_1(sK1)
      | ~ r2_hidden(k1_mcart_1(sK1),sK2) )
    & r2_hidden(sK1,k2_zfmisc_1(sK2,k1_tarski(sK3))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f6,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2] :
        ( ( k2_mcart_1(X0) != X2
          | ~ r2_hidden(k1_mcart_1(X0),X1) )
        & r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))) )
   => ( ( sK3 != k2_mcart_1(sK1)
        | ~ r2_hidden(k1_mcart_1(sK1),sK2) )
      & r2_hidden(sK1,k2_zfmisc_1(sK2,k1_tarski(sK3))) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ( k2_mcart_1(X0) != X2
        | ~ r2_hidden(k1_mcart_1(X0),X1) )
      & r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2)))
       => ( k2_mcart_1(X0) = X2
          & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2)))
     => ( k2_mcart_1(X0) = X2
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_mcart_1)).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k2_tarski(X0,X2))
      | X0 = X1
      | X1 = X2 ) ),
    inference(resolution,[],[f23,f34])).

fof(f34,plain,(
    ! [X0,X1] : sP0(X1,X0,k2_tarski(X0,X1)) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f1,f8])).

fof(f8,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f23,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | X1 = X4
      | ~ r2_hidden(X4,X2)
      | X0 = X4 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ( sK4(X0,X1,X2) != X0
              & sK4(X0,X1,X2) != X1 )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( sK4(X0,X1,X2) = X0
            | sK4(X0,X1,X2) = X1
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f14,f15])).

fof(f15,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X0 != X3
              & X1 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X0 = X3
            | X1 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK4(X0,X1,X2) != X0
            & sK4(X0,X1,X2) != X1 )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( sK4(X0,X1,X2) = X0
          | sK4(X0,X1,X2) = X1
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ( X0 != X3
                & X1 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X0 = X3
              | X1 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f13])).

fof(f13,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f50,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f49])).

fof(f49,plain,
    ( $false
    | spl5_1 ),
    inference(subsumption_resolution,[],[f48,f38])).

fof(f38,plain,
    ( ~ r2_hidden(k1_mcart_1(sK1),sK2)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl5_1
  <=> r2_hidden(k1_mcart_1(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f48,plain,(
    r2_hidden(k1_mcart_1(sK1),sK2) ),
    inference(resolution,[],[f21,f31])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f43,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f19,f40,f36])).

fof(f19,plain,
    ( sK3 != k2_mcart_1(sK1)
    | ~ r2_hidden(k1_mcart_1(sK1),sK2) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:32:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (18879)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.47  % (18887)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.47  % (18887)Refutation not found, incomplete strategy% (18887)------------------------------
% 0.20/0.47  % (18887)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (18887)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (18887)Memory used [KB]: 1663
% 0.20/0.47  % (18887)Time elapsed: 0.081 s
% 0.20/0.47  % (18887)------------------------------
% 0.20/0.47  % (18887)------------------------------
% 0.20/0.48  % (18879)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f60,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f43,f50,f59])).
% 0.20/0.48  fof(f59,plain,(
% 0.20/0.48    spl5_2),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f58])).
% 0.20/0.48  fof(f58,plain,(
% 0.20/0.48    $false | spl5_2),
% 0.20/0.48    inference(subsumption_resolution,[],[f57,f42])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    sK3 != k2_mcart_1(sK1) | spl5_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f40])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    spl5_2 <=> sK3 = k2_mcart_1(sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.48  fof(f57,plain,(
% 0.20/0.48    sK3 = k2_mcart_1(sK1)),
% 0.20/0.48    inference(duplicate_literal_removal,[],[f56])).
% 0.20/0.48  fof(f56,plain,(
% 0.20/0.48    sK3 = k2_mcart_1(sK1) | sK3 = k2_mcart_1(sK1)),
% 0.20/0.48    inference(resolution,[],[f53,f51])).
% 0.20/0.48  fof(f51,plain,(
% 0.20/0.48    r2_hidden(k2_mcart_1(sK1),k2_tarski(sK3,sK3))),
% 0.20/0.48    inference(resolution,[],[f22,f31])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    r2_hidden(sK1,k2_zfmisc_1(sK2,k2_tarski(sK3,sK3)))),
% 0.20/0.48    inference(definition_unfolding,[],[f18,f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    r2_hidden(sK1,k2_zfmisc_1(sK2,k1_tarski(sK3)))),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    (sK3 != k2_mcart_1(sK1) | ~r2_hidden(k1_mcart_1(sK1),sK2)) & r2_hidden(sK1,k2_zfmisc_1(sK2,k1_tarski(sK3)))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f6,f10])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    ? [X0,X1,X2] : ((k2_mcart_1(X0) != X2 | ~r2_hidden(k1_mcart_1(X0),X1)) & r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2)))) => ((sK3 != k2_mcart_1(sK1) | ~r2_hidden(k1_mcart_1(sK1),sK2)) & r2_hidden(sK1,k2_zfmisc_1(sK2,k1_tarski(sK3))))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f6,plain,(
% 0.20/0.48    ? [X0,X1,X2] : ((k2_mcart_1(X0) != X2 | ~r2_hidden(k1_mcart_1(X0),X1)) & r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))))),
% 0.20/0.48    inference(ennf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))) => (k2_mcart_1(X0) = X2 & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.20/0.48    inference(negated_conjecture,[],[f4])).
% 0.20/0.48  fof(f4,conjecture,(
% 0.20/0.48    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))) => (k2_mcart_1(X0) = X2 & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_mcart_1)).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.20/0.48  fof(f53,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X1,k2_tarski(X0,X2)) | X0 = X1 | X1 = X2) )),
% 0.20/0.48    inference(resolution,[],[f23,f34])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ( ! [X0,X1] : (sP0(X1,X0,k2_tarski(X0,X1))) )),
% 0.20/0.48    inference(equality_resolution,[],[f29])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k2_tarski(X0,X1) != X2) )),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k2_tarski(X0,X1) != X2))),
% 0.20/0.48    inference(nnf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 0.20/0.48    inference(definition_folding,[],[f1,f8])).
% 0.20/0.48  fof(f8,plain,(
% 0.20/0.48    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.20/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | X1 = X4 | ~r2_hidden(X4,X2) | X0 = X4) )),
% 0.20/0.48    inference(cnf_transformation,[],[f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (((sK4(X0,X1,X2) != X0 & sK4(X0,X1,X2) != X1) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X0 | sK4(X0,X1,X2) = X1 | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f14,f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ! [X2,X1,X0] : (? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2))) => (((sK4(X0,X1,X2) != X0 & sK4(X0,X1,X2) != X1) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X0 | sK4(X0,X1,X2) = X1 | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.20/0.48    inference(rectify,[],[f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.20/0.48    inference(flattening,[],[f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.20/0.48    inference(nnf_transformation,[],[f8])).
% 0.20/0.48  fof(f50,plain,(
% 0.20/0.48    spl5_1),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f49])).
% 0.20/0.48  fof(f49,plain,(
% 0.20/0.48    $false | spl5_1),
% 0.20/0.48    inference(subsumption_resolution,[],[f48,f38])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    ~r2_hidden(k1_mcart_1(sK1),sK2) | spl5_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f36])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    spl5_1 <=> r2_hidden(k1_mcart_1(sK1),sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    r2_hidden(k1_mcart_1(sK1),sK2)),
% 0.20/0.48    inference(resolution,[],[f21,f31])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f7])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    ~spl5_1 | ~spl5_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f19,f40,f36])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    sK3 != k2_mcart_1(sK1) | ~r2_hidden(k1_mcart_1(sK1),sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (18879)------------------------------
% 0.20/0.48  % (18879)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (18879)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (18879)Memory used [KB]: 10618
% 0.20/0.48  % (18879)Time elapsed: 0.083 s
% 0.20/0.48  % (18879)------------------------------
% 0.20/0.48  % (18879)------------------------------
% 0.20/0.48  % (18872)Success in time 0.12 s
%------------------------------------------------------------------------------
