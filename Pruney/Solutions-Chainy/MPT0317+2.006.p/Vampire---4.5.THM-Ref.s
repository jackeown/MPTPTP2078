%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:14 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 101 expanded)
%              Number of leaves         :   10 (  31 expanded)
%              Depth                    :   11
%              Number of atoms          :  190 ( 367 expanded)
%              Number of equality atoms :   56 ( 116 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f80,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f62,f63,f71,f77,f79])).

fof(f79,plain,
    ( spl5_2
    | ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f78])).

fof(f78,plain,
    ( $false
    | spl5_2
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f75,f52])).

fof(f52,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl5_2
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f75,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl5_4 ),
    inference(resolution,[],[f61,f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f61,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl5_4
  <=> r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f77,plain,
    ( spl5_3
    | ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f76])).

fof(f76,plain,
    ( $false
    | spl5_3
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f74,f73])).

fof(f73,plain,
    ( ~ r2_hidden(sK1,k2_enumset1(sK3,sK3,sK3,sK3))
    | spl5_3 ),
    inference(extensionality_resolution,[],[f43,f56])).

fof(f56,plain,
    ( sK1 != sK3
    | spl5_3 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl5_3
  <=> sK1 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f43,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f24,f23])).

fof(f23,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_enumset1)).

fof(f24,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK4(X0,X1) != X0
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( sK4(X0,X1) = X0
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f13,f14])).

fof(f14,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK4(X0,X1) != X0
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( sK4(X0,X1) = X0
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f74,plain,
    ( r2_hidden(sK1,k2_enumset1(sK3,sK3,sK3,sK3))
    | ~ spl5_4 ),
    inference(resolution,[],[f61,f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f71,plain,
    ( spl5_1
    | ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f70])).

fof(f70,plain,
    ( $false
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f69,f51])).

fof(f51,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f50])).

fof(f69,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl5_1 ),
    inference(subsumption_resolution,[],[f66,f42])).

fof(f42,plain,(
    ! [X3] : r2_hidden(X3,k2_enumset1(X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_enumset1(X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f25,f23])).

fof(f25,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f66,plain,
    ( ~ r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ r2_hidden(sK0,sK2)
    | spl5_1 ),
    inference(resolution,[],[f30,f48])).

fof(f48,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k2_enumset1(sK1,sK1,sK1,sK1)))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl5_1
  <=> r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k2_enumset1(sK1,sK1,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f63,plain,
    ( spl5_4
    | spl5_2 ),
    inference(avatar_split_clause,[],[f36,f50,f59])).

fof(f36,plain,
    ( r2_hidden(sK0,sK2)
    | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) ),
    inference(definition_unfolding,[],[f20,f23])).

fof(f20,plain,
    ( r2_hidden(sK0,sK2)
    | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_tarski(sK3))) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( ( sK1 != sK3
      | ~ r2_hidden(sK0,sK2)
      | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_tarski(sK3))) )
    & ( ( sK1 = sK3
        & r2_hidden(sK0,sK2) )
      | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_tarski(sK3))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( X1 != X3
          | ~ r2_hidden(X0,X2)
          | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) )
        & ( ( X1 = X3
            & r2_hidden(X0,X2) )
          | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) )
   => ( ( sK1 != sK3
        | ~ r2_hidden(sK0,sK2)
        | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_tarski(sK3))) )
      & ( ( sK1 = sK3
          & r2_hidden(sK0,sK2) )
        | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_tarski(sK3))) ) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | ~ r2_hidden(X0,X2)
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) )
      & ( ( X1 = X3
          & r2_hidden(X0,X2) )
        | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | ~ r2_hidden(X0,X2)
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) )
      & ( ( X1 = X3
          & r2_hidden(X0,X2) )
        | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
    <~> ( X1 = X3
        & r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
      <=> ( X1 = X3
          & r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
    <=> ( X1 = X3
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_zfmisc_1)).

fof(f62,plain,
    ( spl5_4
    | spl5_3 ),
    inference(avatar_split_clause,[],[f35,f54,f59])).

fof(f35,plain,
    ( sK1 = sK3
    | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) ),
    inference(definition_unfolding,[],[f21,f23])).

fof(f21,plain,
    ( sK1 = sK3
    | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_tarski(sK3))) ),
    inference(cnf_transformation,[],[f11])).

fof(f57,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f44,f54,f50,f46])).

fof(f44,plain,
    ( sK1 != sK3
    | ~ r2_hidden(sK0,sK2)
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k2_enumset1(sK1,sK1,sK1,sK1))) ),
    inference(inner_rewriting,[],[f34])).

fof(f34,plain,
    ( sK1 != sK3
    | ~ r2_hidden(sK0,sK2)
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) ),
    inference(definition_unfolding,[],[f22,f23])).

fof(f22,plain,
    ( sK1 != sK3
    | ~ r2_hidden(sK0,sK2)
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_tarski(sK3))) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:58:44 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (22308)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (22302)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (22307)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (22309)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (22309)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f57,f62,f63,f71,f77,f79])).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    spl5_2 | ~spl5_4),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f78])).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    $false | (spl5_2 | ~spl5_4)),
% 0.21/0.52    inference(subsumption_resolution,[],[f75,f52])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ~r2_hidden(sK0,sK2) | spl5_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f50])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    spl5_2 <=> r2_hidden(sK0,sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    r2_hidden(sK0,sK2) | ~spl5_4),
% 0.21/0.52    inference(resolution,[],[f61,f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.21/0.52    inference(flattening,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.21/0.52    inference(nnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) | ~spl5_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f59])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    spl5_4 <=> r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    spl5_3 | ~spl5_4),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f76])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    $false | (spl5_3 | ~spl5_4)),
% 0.21/0.52    inference(subsumption_resolution,[],[f74,f73])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    ~r2_hidden(sK1,k2_enumset1(sK3,sK3,sK3,sK3)) | spl5_3),
% 0.21/0.52    inference(extensionality_resolution,[],[f43,f56])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    sK1 != sK3 | spl5_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f54])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    spl5_3 <=> sK1 = sK3),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ( ! [X0,X3] : (~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) | X0 = X3) )),
% 0.21/0.52    inference(equality_resolution,[],[f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 0.21/0.52    inference(definition_unfolding,[],[f24,f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_enumset1)).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f13,f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.52    inference(rectify,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    r2_hidden(sK1,k2_enumset1(sK3,sK3,sK3,sK3)) | ~spl5_4),
% 0.21/0.52    inference(resolution,[],[f61,f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    spl5_1 | ~spl5_2),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f70])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    $false | (spl5_1 | ~spl5_2)),
% 0.21/0.52    inference(subsumption_resolution,[],[f69,f51])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    r2_hidden(sK0,sK2) | ~spl5_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f50])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    ~r2_hidden(sK0,sK2) | spl5_1),
% 0.21/0.52    inference(subsumption_resolution,[],[f66,f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X3] : (r2_hidden(X3,k2_enumset1(X3,X3,X3,X3))) )),
% 0.21/0.52    inference(equality_resolution,[],[f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_enumset1(X3,X3,X3,X3) != X1) )),
% 0.21/0.52    inference(equality_resolution,[],[f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 0.21/0.52    inference(definition_unfolding,[],[f25,f23])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    ~r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) | ~r2_hidden(sK0,sK2) | spl5_1),
% 0.21/0.52    inference(resolution,[],[f30,f48])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k2_enumset1(sK1,sK1,sK1,sK1))) | spl5_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    spl5_1 <=> r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k2_enumset1(sK1,sK1,sK1,sK1)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    spl5_4 | spl5_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f36,f50,f59])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    r2_hidden(sK0,sK2) | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))),
% 0.21/0.52    inference(definition_unfolding,[],[f20,f23])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    r2_hidden(sK0,sK2) | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_tarski(sK3)))),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    (sK1 != sK3 | ~r2_hidden(sK0,sK2) | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_tarski(sK3)))) & ((sK1 = sK3 & r2_hidden(sK0,sK2)) | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_tarski(sK3))))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f10])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3] : ((X1 != X3 | ~r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))) & ((X1 = X3 & r2_hidden(X0,X2)) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))))) => ((sK1 != sK3 | ~r2_hidden(sK0,sK2) | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_tarski(sK3)))) & ((sK1 = sK3 & r2_hidden(sK0,sK2)) | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_tarski(sK3)))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3] : ((X1 != X3 | ~r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))) & ((X1 = X3 & r2_hidden(X0,X2)) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))))),
% 0.21/0.52    inference(flattening,[],[f8])).
% 0.21/0.52  fof(f8,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3] : (((X1 != X3 | ~r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))) & ((X1 = X3 & r2_hidden(X0,X2)) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))))),
% 0.21/0.52    inference(nnf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,plain,(
% 0.21/0.52    ? [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) <~> (X1 = X3 & r2_hidden(X0,X2)))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) <=> (X1 = X3 & r2_hidden(X0,X2)))),
% 0.21/0.52    inference(negated_conjecture,[],[f5])).
% 0.21/0.52  fof(f5,conjecture,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) <=> (X1 = X3 & r2_hidden(X0,X2)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_zfmisc_1)).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    spl5_4 | spl5_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f35,f54,f59])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    sK1 = sK3 | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))),
% 0.21/0.52    inference(definition_unfolding,[],[f21,f23])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    sK1 = sK3 | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_tarski(sK3)))),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ~spl5_1 | ~spl5_2 | ~spl5_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f44,f54,f50,f46])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    sK1 != sK3 | ~r2_hidden(sK0,sK2) | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k2_enumset1(sK1,sK1,sK1,sK1)))),
% 0.21/0.52    inference(inner_rewriting,[],[f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    sK1 != sK3 | ~r2_hidden(sK0,sK2) | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))),
% 0.21/0.52    inference(definition_unfolding,[],[f22,f23])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    sK1 != sK3 | ~r2_hidden(sK0,sK2) | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_tarski(sK3)))),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (22309)------------------------------
% 0.21/0.52  % (22309)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (22309)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (22309)Memory used [KB]: 10746
% 0.21/0.52  % (22309)Time elapsed: 0.116 s
% 0.21/0.52  % (22309)------------------------------
% 0.21/0.52  % (22309)------------------------------
% 0.21/0.53  % (22312)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.53  % (22301)Success in time 0.169 s
%------------------------------------------------------------------------------
