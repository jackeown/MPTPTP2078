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
% DateTime   : Thu Dec  3 12:41:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   39 (  59 expanded)
%              Number of leaves         :   12 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :  138 ( 186 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f69,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f40,f55,f60,f68])).

fof(f68,plain,
    ( spl6_3
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f61,f57,f37,f52])).

fof(f52,plain,
    ( spl6_3
  <=> r2_hidden(sK2(sK0,k3_tarski(sK1)),k3_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f37,plain,
    ( spl6_2
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f57,plain,
    ( spl6_4
  <=> r2_hidden(sK2(sK0,k3_tarski(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f61,plain,
    ( r2_hidden(sK2(sK0,k3_tarski(sK1)),k3_tarski(sK1))
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f39,f59,f28])).

fof(f28,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k3_tarski(X0))
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK3(X0,X1),X3) )
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( ( r2_hidden(sK4(X0,X1),X0)
              & r2_hidden(sK3(X0,X1),sK4(X0,X1)) )
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK5(X0,X5),X0)
                & r2_hidden(X5,sK5(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f13,f16,f15,f14])).

fof(f14,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X3) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( r2_hidden(X4,X0)
                & r2_hidden(X2,X4) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(sK3(X0,X1),X3) )
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK3(X0,X1),X4) )
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(sK3(X0,X1),X4) )
     => ( r2_hidden(sK4(X0,X1),X0)
        & r2_hidden(sK3(X0,X1),sK4(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK5(X0,X5),X0)
        & r2_hidden(X5,sK5(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X0)
                  & r2_hidden(X2,X4) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ? [X7] :
                  ( r2_hidden(X7,X0)
                  & r2_hidden(X5,X7) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) ) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

fof(f59,plain,
    ( r2_hidden(sK2(sK0,k3_tarski(sK1)),sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f57])).

fof(f39,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f60,plain,
    ( spl6_4
    | spl6_1 ),
    inference(avatar_split_clause,[],[f44,f32,f57])).

fof(f32,plain,
    ( spl6_1
  <=> r1_tarski(sK0,k3_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f44,plain,
    ( r2_hidden(sK2(sK0,k3_tarski(sK1)),sK0)
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f34,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f7,f10])).

fof(f10,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f34,plain,
    ( ~ r1_tarski(sK0,k3_tarski(sK1))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f55,plain,
    ( ~ spl6_3
    | spl6_1 ),
    inference(avatar_split_clause,[],[f45,f32,f52])).

fof(f45,plain,
    ( ~ r2_hidden(sK2(sK0,k3_tarski(sK1)),k3_tarski(sK1))
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f34,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f40,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f18,f37])).

fof(f18,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,
    ( ~ r1_tarski(sK0,k3_tarski(sK1))
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f8])).

fof(f8,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(X0,k3_tarski(X1))
        & r2_hidden(X0,X1) )
   => ( ~ r1_tarski(sK0,k3_tarski(sK1))
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k3_tarski(X1))
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => r1_tarski(X0,k3_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_zfmisc_1)).

fof(f35,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f19,f32])).

fof(f19,plain,(
    ~ r1_tarski(sK0,k3_tarski(sK1)) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n013.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:35:09 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.55  % (4766)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.56  % (4758)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.57  % (4750)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.57  % (4744)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.57  % (4766)Refutation found. Thanks to Tanya!
% 0.21/0.57  % SZS status Theorem for theBenchmark
% 0.21/0.57  % SZS output start Proof for theBenchmark
% 0.21/0.57  fof(f69,plain,(
% 0.21/0.57    $false),
% 0.21/0.57    inference(avatar_sat_refutation,[],[f35,f40,f55,f60,f68])).
% 0.21/0.57  fof(f68,plain,(
% 0.21/0.57    spl6_3 | ~spl6_2 | ~spl6_4),
% 0.21/0.57    inference(avatar_split_clause,[],[f61,f57,f37,f52])).
% 0.21/0.57  fof(f52,plain,(
% 0.21/0.57    spl6_3 <=> r2_hidden(sK2(sK0,k3_tarski(sK1)),k3_tarski(sK1))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.57  fof(f37,plain,(
% 0.21/0.57    spl6_2 <=> r2_hidden(sK0,sK1)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.57  fof(f57,plain,(
% 0.21/0.57    spl6_4 <=> r2_hidden(sK2(sK0,k3_tarski(sK1)),sK0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.57  fof(f61,plain,(
% 0.21/0.57    r2_hidden(sK2(sK0,k3_tarski(sK1)),k3_tarski(sK1)) | (~spl6_2 | ~spl6_4)),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f39,f59,f28])).
% 0.21/0.57  fof(f28,plain,(
% 0.21/0.57    ( ! [X6,X0,X5] : (r2_hidden(X5,k3_tarski(X0)) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X6)) )),
% 0.21/0.57    inference(equality_resolution,[],[f24])).
% 0.21/0.57  fof(f24,plain,(
% 0.21/0.57    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X6) | k3_tarski(X0) != X1) )),
% 0.21/0.57    inference(cnf_transformation,[],[f17])).
% 0.21/0.57  fof(f17,plain,(
% 0.21/0.57    ! [X0,X1] : ((k3_tarski(X0) = X1 | ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK3(X0,X1),X3)) | ~r2_hidden(sK3(X0,X1),X1)) & ((r2_hidden(sK4(X0,X1),X0) & r2_hidden(sK3(X0,X1),sK4(X0,X1))) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & ((r2_hidden(sK5(X0,X5),X0) & r2_hidden(X5,sK5(X0,X5))) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f13,f16,f15,f14])).
% 0.21/0.57  fof(f14,plain,(
% 0.21/0.57    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1))) => ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK3(X0,X1),X3)) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK3(X0,X1),X4)) | r2_hidden(sK3(X0,X1),X1))))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f15,plain,(
% 0.21/0.57    ! [X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK3(X0,X1),X4)) => (r2_hidden(sK4(X0,X1),X0) & r2_hidden(sK3(X0,X1),sK4(X0,X1))))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f16,plain,(
% 0.21/0.57    ! [X5,X0] : (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) => (r2_hidden(sK5(X0,X5),X0) & r2_hidden(X5,sK5(X0,X5))))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f13,plain,(
% 0.21/0.57    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 0.21/0.57    inference(rectify,[],[f12])).
% 0.21/0.57  fof(f12,plain,(
% 0.21/0.57    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~r2_hidden(X2,X1))) | k3_tarski(X0) != X1))),
% 0.21/0.57    inference(nnf_transformation,[],[f2])).
% 0.21/0.57  fof(f2,axiom,(
% 0.21/0.57    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).
% 0.21/0.57  fof(f59,plain,(
% 0.21/0.57    r2_hidden(sK2(sK0,k3_tarski(sK1)),sK0) | ~spl6_4),
% 0.21/0.57    inference(avatar_component_clause,[],[f57])).
% 0.21/0.57  fof(f39,plain,(
% 0.21/0.57    r2_hidden(sK0,sK1) | ~spl6_2),
% 0.21/0.57    inference(avatar_component_clause,[],[f37])).
% 0.21/0.57  fof(f60,plain,(
% 0.21/0.57    spl6_4 | spl6_1),
% 0.21/0.57    inference(avatar_split_clause,[],[f44,f32,f57])).
% 0.21/0.57  fof(f32,plain,(
% 0.21/0.57    spl6_1 <=> r1_tarski(sK0,k3_tarski(sK1))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.57  fof(f44,plain,(
% 0.21/0.57    r2_hidden(sK2(sK0,k3_tarski(sK1)),sK0) | spl6_1),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f34,f20])).
% 0.21/0.57  fof(f20,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f11])).
% 0.21/0.57  fof(f11,plain,(
% 0.21/0.57    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f7,f10])).
% 0.21/0.57  fof(f10,plain,(
% 0.21/0.57    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f7,plain,(
% 0.21/0.57    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f5])).
% 0.21/0.57  fof(f5,plain,(
% 0.21/0.57    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 0.21/0.57    inference(unused_predicate_definition_removal,[],[f1])).
% 0.21/0.57  fof(f1,axiom,(
% 0.21/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.57  fof(f34,plain,(
% 0.21/0.57    ~r1_tarski(sK0,k3_tarski(sK1)) | spl6_1),
% 0.21/0.57    inference(avatar_component_clause,[],[f32])).
% 0.21/0.57  fof(f55,plain,(
% 0.21/0.57    ~spl6_3 | spl6_1),
% 0.21/0.57    inference(avatar_split_clause,[],[f45,f32,f52])).
% 0.21/0.57  fof(f45,plain,(
% 0.21/0.57    ~r2_hidden(sK2(sK0,k3_tarski(sK1)),k3_tarski(sK1)) | spl6_1),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f34,f21])).
% 0.21/0.57  fof(f21,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK2(X0,X1),X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f11])).
% 0.21/0.57  fof(f40,plain,(
% 0.21/0.57    spl6_2),
% 0.21/0.57    inference(avatar_split_clause,[],[f18,f37])).
% 0.21/0.57  fof(f18,plain,(
% 0.21/0.57    r2_hidden(sK0,sK1)),
% 0.21/0.57    inference(cnf_transformation,[],[f9])).
% 0.21/0.57  fof(f9,plain,(
% 0.21/0.57    ~r1_tarski(sK0,k3_tarski(sK1)) & r2_hidden(sK0,sK1)),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f8])).
% 0.21/0.57  fof(f8,plain,(
% 0.21/0.57    ? [X0,X1] : (~r1_tarski(X0,k3_tarski(X1)) & r2_hidden(X0,X1)) => (~r1_tarski(sK0,k3_tarski(sK1)) & r2_hidden(sK0,sK1))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f6,plain,(
% 0.21/0.57    ? [X0,X1] : (~r1_tarski(X0,k3_tarski(X1)) & r2_hidden(X0,X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f4])).
% 0.21/0.57  fof(f4,negated_conjecture,(
% 0.21/0.57    ~! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 0.21/0.57    inference(negated_conjecture,[],[f3])).
% 0.21/0.57  fof(f3,conjecture,(
% 0.21/0.57    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_zfmisc_1)).
% 0.21/0.57  fof(f35,plain,(
% 0.21/0.57    ~spl6_1),
% 0.21/0.57    inference(avatar_split_clause,[],[f19,f32])).
% 0.21/0.57  fof(f19,plain,(
% 0.21/0.57    ~r1_tarski(sK0,k3_tarski(sK1))),
% 0.21/0.57    inference(cnf_transformation,[],[f9])).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (4766)------------------------------
% 0.21/0.57  % (4766)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (4766)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (4766)Memory used [KB]: 6268
% 0.21/0.57  % (4766)Time elapsed: 0.142 s
% 0.21/0.57  % (4766)------------------------------
% 0.21/0.57  % (4766)------------------------------
% 0.21/0.57  % (4752)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.57  % (4740)Success in time 0.21 s
%------------------------------------------------------------------------------
