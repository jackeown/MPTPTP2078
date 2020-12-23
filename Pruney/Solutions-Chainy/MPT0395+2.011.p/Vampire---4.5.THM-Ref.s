%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:05 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   42 (  85 expanded)
%              Number of leaves         :    8 (  25 expanded)
%              Depth                    :   11
%              Number of atoms          :  117 ( 264 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f50,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f36,f45,f49])).

fof(f49,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f48])).

fof(f48,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f47,f34])).

fof(f34,plain,
    ( r2_hidden(sK2(sK0,sK1),sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl4_2
  <=> r2_hidden(sK2(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f47,plain,
    ( ~ r2_hidden(sK2(sK0,sK1),sK1)
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f46,f18])).

fof(f18,plain,(
    ~ r1_setfam_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( ~ r1_setfam_1(sK0,sK1)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f9])).

fof(f9,plain,
    ( ? [X0,X1] :
        ( ~ r1_setfam_1(X0,X1)
        & r1_tarski(X0,X1) )
   => ( ~ r1_setfam_1(sK0,sK1)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ~ r1_setfam_1(X0,X1)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,X1)
       => r1_setfam_1(X0,X1) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_setfam_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_setfam_1)).

fof(f46,plain,
    ( r1_setfam_1(sK0,sK1)
    | ~ r2_hidden(sK2(sK0,sK1),sK1)
    | ~ spl4_1 ),
    inference(resolution,[],[f31,f20])).

fof(f20,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(sK2(X0,X1),X3)
      | r1_setfam_1(X0,X1)
      | ~ r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
      | ( ! [X3] :
            ( ~ r1_tarski(sK2(X0,X1),X3)
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f7,f11])).

fof(f11,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r1_tarski(X2,X3)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X0) )
     => ( ! [X3] :
            ( ~ r1_tarski(sK2(X0,X1),X3)
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
      | ? [X2] :
          ( ! [X3] :
              ( ~ r1_tarski(X2,X3)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) )
     => r1_setfam_1(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).

fof(f31,plain,
    ( r1_tarski(sK2(sK0,sK1),sK2(sK0,sK1))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f29])).

fof(f29,plain,
    ( spl4_1
  <=> r1_tarski(sK2(sK0,sK1),sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f45,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f44])).

fof(f44,plain,
    ( $false
    | spl4_2 ),
    inference(subsumption_resolution,[],[f43,f18])).

fof(f43,plain,
    ( r1_setfam_1(sK0,sK1)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f41,f17])).

fof(f17,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f41,plain,
    ( ~ r1_tarski(sK0,sK1)
    | r1_setfam_1(sK0,sK1)
    | spl4_2 ),
    inference(resolution,[],[f37,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f37,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2(sK0,sK1),X0)
        | ~ r1_tarski(X0,sK1) )
    | spl4_2 ),
    inference(resolution,[],[f35,f21])).

fof(f21,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f15])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f35,plain,
    ( ~ r2_hidden(sK2(sK0,sK1),sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f33])).

fof(f36,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f26,f33,f29])).

fof(f26,plain,
    ( ~ r2_hidden(sK2(sK0,sK1),sK1)
    | r1_tarski(sK2(sK0,sK1),sK2(sK0,sK1)) ),
    inference(resolution,[],[f25,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f25,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(sK2(sK0,sK1),X0),X0)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f24,f18])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r1_setfam_1(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(sK3(sK2(X0,X1),X2),X2) ) ),
    inference(resolution,[],[f20,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.33  % Computer   : n022.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:30:25 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.44  % (22186)lrs+1003_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=on:fde=unused:gs=on:inw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.45  % (22194)dis+1011_4_awrs=decay:awrsf=32:afp=40000:afq=1.0:amm=off:anc=all:bs=on:cond=on:fsr=off:gsp=input_only:lma=on:nm=16:nwc=1:nicw=on:sac=on:sp=frequency:thi=all:updr=off:uhcvi=on_670 on theBenchmark
% 0.20/0.46  % (22178)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.20/0.46  % (22178)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f50,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(avatar_sat_refutation,[],[f36,f45,f49])).
% 0.20/0.46  fof(f49,plain,(
% 0.20/0.46    ~spl4_1 | ~spl4_2),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f48])).
% 0.20/0.46  fof(f48,plain,(
% 0.20/0.46    $false | (~spl4_1 | ~spl4_2)),
% 0.20/0.46    inference(subsumption_resolution,[],[f47,f34])).
% 0.20/0.46  fof(f34,plain,(
% 0.20/0.46    r2_hidden(sK2(sK0,sK1),sK1) | ~spl4_2),
% 0.20/0.46    inference(avatar_component_clause,[],[f33])).
% 0.20/0.46  fof(f33,plain,(
% 0.20/0.46    spl4_2 <=> r2_hidden(sK2(sK0,sK1),sK1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.46  fof(f47,plain,(
% 0.20/0.46    ~r2_hidden(sK2(sK0,sK1),sK1) | ~spl4_1),
% 0.20/0.46    inference(subsumption_resolution,[],[f46,f18])).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    ~r1_setfam_1(sK0,sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f10])).
% 0.20/0.46  fof(f10,plain,(
% 0.20/0.46    ~r1_setfam_1(sK0,sK1) & r1_tarski(sK0,sK1)),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f9])).
% 0.20/0.46  fof(f9,plain,(
% 0.20/0.46    ? [X0,X1] : (~r1_setfam_1(X0,X1) & r1_tarski(X0,X1)) => (~r1_setfam_1(sK0,sK1) & r1_tarski(sK0,sK1))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f6,plain,(
% 0.20/0.46    ? [X0,X1] : (~r1_setfam_1(X0,X1) & r1_tarski(X0,X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f4])).
% 0.20/0.46  fof(f4,negated_conjecture,(
% 0.20/0.46    ~! [X0,X1] : (r1_tarski(X0,X1) => r1_setfam_1(X0,X1))),
% 0.20/0.46    inference(negated_conjecture,[],[f3])).
% 0.20/0.46  fof(f3,conjecture,(
% 0.20/0.46    ! [X0,X1] : (r1_tarski(X0,X1) => r1_setfam_1(X0,X1))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_setfam_1)).
% 0.20/0.46  fof(f46,plain,(
% 0.20/0.46    r1_setfam_1(sK0,sK1) | ~r2_hidden(sK2(sK0,sK1),sK1) | ~spl4_1),
% 0.20/0.46    inference(resolution,[],[f31,f20])).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    ( ! [X0,X3,X1] : (~r1_tarski(sK2(X0,X1),X3) | r1_setfam_1(X0,X1) | ~r2_hidden(X3,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f12])).
% 0.20/0.46  fof(f12,plain,(
% 0.20/0.46    ! [X0,X1] : (r1_setfam_1(X0,X1) | (! [X3] : (~r1_tarski(sK2(X0,X1),X3) | ~r2_hidden(X3,X1)) & r2_hidden(sK2(X0,X1),X0)))),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f7,f11])).
% 0.20/0.46  fof(f11,plain,(
% 0.20/0.46    ! [X1,X0] : (? [X2] : (! [X3] : (~r1_tarski(X2,X3) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X0)) => (! [X3] : (~r1_tarski(sK2(X0,X1),X3) | ~r2_hidden(X3,X1)) & r2_hidden(sK2(X0,X1),X0)))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f7,plain,(
% 0.20/0.46    ! [X0,X1] : (r1_setfam_1(X0,X1) | ? [X2] : (! [X3] : (~r1_tarski(X2,X3) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f5])).
% 0.20/0.46  fof(f5,plain,(
% 0.20/0.46    ! [X0,X1] : (! [X2] : ~(! [X3] : ~(r1_tarski(X2,X3) & r2_hidden(X3,X1)) & r2_hidden(X2,X0)) => r1_setfam_1(X0,X1))),
% 0.20/0.46    inference(unused_predicate_definition_removal,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0,X1] : (r1_setfam_1(X0,X1) <=> ! [X2] : ~(! [X3] : ~(r1_tarski(X2,X3) & r2_hidden(X3,X1)) & r2_hidden(X2,X0)))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).
% 0.20/0.46  fof(f31,plain,(
% 0.20/0.46    r1_tarski(sK2(sK0,sK1),sK2(sK0,sK1)) | ~spl4_1),
% 0.20/0.46    inference(avatar_component_clause,[],[f29])).
% 0.20/0.46  fof(f29,plain,(
% 0.20/0.46    spl4_1 <=> r1_tarski(sK2(sK0,sK1),sK2(sK0,sK1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.46  fof(f45,plain,(
% 0.20/0.46    spl4_2),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f44])).
% 0.20/0.46  fof(f44,plain,(
% 0.20/0.46    $false | spl4_2),
% 0.20/0.46    inference(subsumption_resolution,[],[f43,f18])).
% 0.20/0.46  fof(f43,plain,(
% 0.20/0.46    r1_setfam_1(sK0,sK1) | spl4_2),
% 0.20/0.46    inference(subsumption_resolution,[],[f41,f17])).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    r1_tarski(sK0,sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f10])).
% 0.20/0.46  fof(f41,plain,(
% 0.20/0.46    ~r1_tarski(sK0,sK1) | r1_setfam_1(sK0,sK1) | spl4_2),
% 0.20/0.46    inference(resolution,[],[f37,f19])).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_setfam_1(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f12])).
% 0.20/0.46  fof(f37,plain,(
% 0.20/0.46    ( ! [X0] : (~r2_hidden(sK2(sK0,sK1),X0) | ~r1_tarski(X0,sK1)) ) | spl4_2),
% 0.20/0.46    inference(resolution,[],[f35,f21])).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f16])).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f15])).
% 0.20/0.46  fof(f15,plain,(
% 0.20/0.46    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.46    inference(rectify,[],[f13])).
% 0.20/0.46  fof(f13,plain,(
% 0.20/0.46    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.46    inference(nnf_transformation,[],[f8])).
% 0.20/0.46  fof(f8,plain,(
% 0.20/0.46    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.46  fof(f35,plain,(
% 0.20/0.46    ~r2_hidden(sK2(sK0,sK1),sK1) | spl4_2),
% 0.20/0.46    inference(avatar_component_clause,[],[f33])).
% 0.20/0.46  fof(f36,plain,(
% 0.20/0.46    spl4_1 | ~spl4_2),
% 0.20/0.46    inference(avatar_split_clause,[],[f26,f33,f29])).
% 0.20/0.46  fof(f26,plain,(
% 0.20/0.46    ~r2_hidden(sK2(sK0,sK1),sK1) | r1_tarski(sK2(sK0,sK1),sK2(sK0,sK1))),
% 0.20/0.46    inference(resolution,[],[f25,f22])).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f16])).
% 0.20/0.46  fof(f25,plain,(
% 0.20/0.46    ( ! [X0] : (~r2_hidden(sK3(sK2(sK0,sK1),X0),X0) | ~r2_hidden(X0,sK1)) )),
% 0.20/0.46    inference(resolution,[],[f24,f18])).
% 0.20/0.46  fof(f24,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (r1_setfam_1(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(sK3(sK2(X0,X1),X2),X2)) )),
% 0.20/0.46    inference(resolution,[],[f20,f23])).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK3(X0,X1),X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f16])).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (22178)------------------------------
% 0.20/0.46  % (22178)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (22178)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (22178)Memory used [KB]: 5373
% 0.20/0.46  % (22178)Time elapsed: 0.054 s
% 0.20/0.46  % (22178)------------------------------
% 0.20/0.46  % (22178)------------------------------
% 0.20/0.46  % (22177)Success in time 0.111 s
%------------------------------------------------------------------------------
