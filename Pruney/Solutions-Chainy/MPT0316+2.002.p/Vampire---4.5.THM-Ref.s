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
% DateTime   : Thu Dec  3 12:42:11 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   49 (  87 expanded)
%              Number of leaves         :    8 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :  175 ( 350 expanded)
%              Number of equality atoms :   48 ( 101 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f116,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f55,f56,f87,f114,f115])).

fof(f115,plain,
    ( spl5_3
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f107,f43,f51])).

fof(f51,plain,
    ( spl5_3
  <=> r2_hidden(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f43,plain,
    ( spl5_1
  <=> r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f107,plain,
    ( r2_hidden(sK1,sK3)
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f44,f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(f44,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f43])).

fof(f114,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_contradiction_clause,[],[f113])).

fof(f113,plain,
    ( $false
    | ~ spl5_1
    | spl5_2 ),
    inference(subsumption_resolution,[],[f108,f106])).

fof(f106,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK2))
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f49,f41])).

fof(f41,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f26,f27])).

fof(f27,plain,(
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

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f49,plain,
    ( sK0 != sK2
    | spl5_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl5_2
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f108,plain,
    ( r2_hidden(sK0,k1_tarski(sK2))
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f44,f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f87,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_contradiction_clause,[],[f86])).

fof(f86,plain,
    ( $false
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f85,f40])).

fof(f40,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f85,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK0))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f78,f52])).

fof(f52,plain,
    ( r2_hidden(sK1,sK3)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f51])).

fof(f78,plain,
    ( ~ r2_hidden(sK1,sK3)
    | ~ r2_hidden(sK0,k1_tarski(sK0))
    | spl5_1
    | ~ spl5_2 ),
    inference(resolution,[],[f34,f57])).

fof(f57,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),sK3))
    | spl5_1
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f45,f48])).

fof(f48,plain,
    ( sK0 = sK2
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f45,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f43])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f56,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f29,f47,f43])).

fof(f29,plain,
    ( sK0 = sK2
    | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ( ~ r2_hidden(sK1,sK3)
      | sK0 != sK2
      | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3)) )
    & ( ( r2_hidden(sK1,sK3)
        & sK0 = sK2 )
      | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f21])).

fof(f21,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ r2_hidden(X1,X3)
          | X0 != X2
          | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) )
        & ( ( r2_hidden(X1,X3)
            & X0 = X2 )
          | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) )
   => ( ( ~ r2_hidden(sK1,sK3)
        | sK0 != sK2
        | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3)) )
      & ( ( r2_hidden(sK1,sK3)
          & sK0 = sK2 )
        | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r2_hidden(X1,X3)
        | X0 != X2
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) )
      & ( ( r2_hidden(X1,X3)
          & X0 = X2 )
        | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r2_hidden(X1,X3)
        | X0 != X2
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) )
      & ( ( r2_hidden(X1,X3)
          & X0 = X2 )
        | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
    <~> ( r2_hidden(X1,X3)
        & X0 = X2 ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
      <=> ( r2_hidden(X1,X3)
          & X0 = X2 ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
    <=> ( r2_hidden(X1,X3)
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_zfmisc_1)).

fof(f55,plain,
    ( spl5_1
    | spl5_3 ),
    inference(avatar_split_clause,[],[f30,f51,f43])).

fof(f30,plain,
    ( r2_hidden(sK1,sK3)
    | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3)) ),
    inference(cnf_transformation,[],[f22])).

fof(f54,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f31,f51,f47,f43])).

fof(f31,plain,
    ( ~ r2_hidden(sK1,sK3)
    | sK0 != sK2
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3)) ),
    inference(cnf_transformation,[],[f22])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 16:11:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (22982)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.51  % (22997)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.51  % (22984)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.51  % (22984)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f116,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f54,f55,f56,f87,f114,f115])).
% 0.22/0.51  fof(f115,plain,(
% 0.22/0.51    spl5_3 | ~spl5_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f107,f43,f51])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    spl5_3 <=> r2_hidden(sK1,sK3)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    spl5_1 <=> r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.51  fof(f107,plain,(
% 0.22/0.51    r2_hidden(sK1,sK3) | ~spl5_1),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f44,f33])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.22/0.51    inference(flattening,[],[f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.22/0.51    inference(nnf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,axiom,(
% 0.22/0.51    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_zfmisc_1)).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3)) | ~spl5_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f43])).
% 0.22/0.51  fof(f114,plain,(
% 0.22/0.51    ~spl5_1 | spl5_2),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f113])).
% 0.22/0.51  fof(f113,plain,(
% 0.22/0.51    $false | (~spl5_1 | spl5_2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f108,f106])).
% 0.22/0.51  fof(f106,plain,(
% 0.22/0.51    ~r2_hidden(sK0,k1_tarski(sK2)) | spl5_2),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f49,f41])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 0.22/0.51    inference(equality_resolution,[],[f35])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.22/0.51    inference(cnf_transformation,[],[f28])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f26,f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.51    inference(rectify,[],[f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.51    inference(nnf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    sK0 != sK2 | spl5_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f47])).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    spl5_2 <=> sK0 = sK2),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.51  fof(f108,plain,(
% 0.22/0.51    r2_hidden(sK0,k1_tarski(sK2)) | ~spl5_1),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f44,f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f24])).
% 0.22/0.51  fof(f87,plain,(
% 0.22/0.51    spl5_1 | ~spl5_2 | ~spl5_3),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f86])).
% 0.22/0.51  fof(f86,plain,(
% 0.22/0.51    $false | (spl5_1 | ~spl5_2 | ~spl5_3)),
% 0.22/0.51    inference(subsumption_resolution,[],[f85,f40])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 0.22/0.51    inference(equality_resolution,[],[f39])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 0.22/0.51    inference(equality_resolution,[],[f36])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 0.22/0.51    inference(cnf_transformation,[],[f28])).
% 0.22/0.51  fof(f85,plain,(
% 0.22/0.51    ~r2_hidden(sK0,k1_tarski(sK0)) | (spl5_1 | ~spl5_2 | ~spl5_3)),
% 0.22/0.51    inference(subsumption_resolution,[],[f78,f52])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    r2_hidden(sK1,sK3) | ~spl5_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f51])).
% 0.22/0.51  fof(f78,plain,(
% 0.22/0.51    ~r2_hidden(sK1,sK3) | ~r2_hidden(sK0,k1_tarski(sK0)) | (spl5_1 | ~spl5_2)),
% 0.22/0.51    inference(resolution,[],[f34,f57])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK0),sK3)) | (spl5_1 | ~spl5_2)),
% 0.22/0.51    inference(forward_demodulation,[],[f45,f48])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    sK0 = sK2 | ~spl5_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f47])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3)) | spl5_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f43])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f24])).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    spl5_1 | spl5_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f29,f47,f43])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    sK0 = sK2 | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3))),
% 0.22/0.51    inference(cnf_transformation,[],[f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    (~r2_hidden(sK1,sK3) | sK0 != sK2 | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3))) & ((r2_hidden(sK1,sK3) & sK0 = sK2) | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3)))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ? [X0,X1,X2,X3] : ((~r2_hidden(X1,X3) | X0 != X2 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))) & ((r2_hidden(X1,X3) & X0 = X2) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)))) => ((~r2_hidden(sK1,sK3) | sK0 != sK2 | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3))) & ((r2_hidden(sK1,sK3) & sK0 = sK2) | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ? [X0,X1,X2,X3] : ((~r2_hidden(X1,X3) | X0 != X2 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))) & ((r2_hidden(X1,X3) & X0 = X2) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))))),
% 0.22/0.51    inference(flattening,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ? [X0,X1,X2,X3] : (((~r2_hidden(X1,X3) | X0 != X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))) & ((r2_hidden(X1,X3) & X0 = X2) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))))),
% 0.22/0.51    inference(nnf_transformation,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ? [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) <~> (r2_hidden(X1,X3) & X0 = X2))),
% 0.22/0.51    inference(ennf_transformation,[],[f17])).
% 0.22/0.51  fof(f17,negated_conjecture,(
% 0.22/0.51    ~! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) <=> (r2_hidden(X1,X3) & X0 = X2))),
% 0.22/0.51    inference(negated_conjecture,[],[f16])).
% 0.22/0.51  fof(f16,conjecture,(
% 0.22/0.51    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) <=> (r2_hidden(X1,X3) & X0 = X2))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_zfmisc_1)).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    spl5_1 | spl5_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f30,f51,f43])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    r2_hidden(sK1,sK3) | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3))),
% 0.22/0.51    inference(cnf_transformation,[],[f22])).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    ~spl5_1 | ~spl5_2 | ~spl5_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f31,f51,f47,f43])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ~r2_hidden(sK1,sK3) | sK0 != sK2 | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3))),
% 0.22/0.51    inference(cnf_transformation,[],[f22])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (22984)------------------------------
% 0.22/0.51  % (22984)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (22984)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (22984)Memory used [KB]: 10746
% 0.22/0.51  % (22984)Time elapsed: 0.101 s
% 0.22/0.51  % (22984)------------------------------
% 0.22/0.51  % (22984)------------------------------
% 1.24/0.52  % (22972)Success in time 0.156 s
%------------------------------------------------------------------------------
