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

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   45 (  61 expanded)
%              Number of leaves         :   10 (  18 expanded)
%              Depth                    :   14
%              Number of atoms          :  134 ( 198 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f105,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f39,f44,f104])).

fof(f104,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_contradiction_clause,[],[f103])).

fof(f103,plain,
    ( $false
    | ~ spl4_1
    | spl4_2 ),
    inference(subsumption_resolution,[],[f99,f38])).

fof(f38,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl4_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f99,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl4_2 ),
    inference(resolution,[],[f97,f43])).

fof(f43,plain,
    ( ~ r1_setfam_1(sK0,sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl4_2
  <=> r1_setfam_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f97,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
      | ~ r1_tarski(X0,X1)
      | r1_setfam_1(X0,X1) ) ),
    inference(resolution,[],[f76,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_setfam_1(X0,X1) ) ),
    inference(resolution,[],[f29,f33])).

fof(f33,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f29,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(sK2(X0,X1),X3)
      | r1_setfam_1(X0,X1)
      | ~ r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_setfam_1(X0,X1)
        | ( ! [X3] :
              ( ~ r1_tarski(sK2(X0,X1),X3)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X4] :
            ( ( r1_tarski(X4,sK3(X1,X4))
              & r2_hidden(sK3(X1,X4),X1) )
            | ~ r2_hidden(X4,X0) )
        | ~ r1_setfam_1(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f16,f18,f17])).

fof(f17,plain,(
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

fof(f18,plain,(
    ! [X4,X1] :
      ( ? [X5] :
          ( r1_tarski(X4,X5)
          & r2_hidden(X5,X1) )
     => ( r1_tarski(X4,sK3(X1,X4))
        & r2_hidden(sK3(X1,X4),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_setfam_1(X0,X1)
        | ? [X2] :
            ( ! [X3] :
                ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) )
      & ( ! [X4] :
            ( ? [X5] :
                ( r1_tarski(X4,X5)
                & r2_hidden(X5,X1) )
            | ~ r2_hidden(X4,X0) )
        | ~ r1_setfam_1(X0,X1) ) ) ),
    inference(rectify,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_setfam_1(X0,X1)
        | ? [X2] :
            ( ! [X3] :
                ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( ? [X3] :
                ( r1_tarski(X2,X3)
                & r2_hidden(X3,X1) )
            | ~ r2_hidden(X2,X0) )
        | ~ r1_setfam_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ( ? [X3] :
              ( r1_tarski(X2,X3)
              & r2_hidden(X3,X1) )
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X2),X1)
      | r1_setfam_1(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f72,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f72,plain,(
    ! [X4,X2,X3] :
      ( r1_tarski(k1_tarski(sK2(X2,X3)),X4)
      | ~ r1_tarski(X2,X4)
      | r1_setfam_1(X2,X3) ) ),
    inference(resolution,[],[f47,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(sK2(X0,X1)),X0)
      | r1_setfam_1(X0,X1) ) ),
    inference(resolution,[],[f28,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f44,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f22,f41])).

fof(f22,plain,(
    ~ r1_setfam_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ~ r1_setfam_1(sK0,sK1)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f11])).

fof(f11,plain,
    ( ? [X0,X1] :
        ( ~ r1_setfam_1(X0,X1)
        & r1_tarski(X0,X1) )
   => ( ~ r1_setfam_1(sK0,sK1)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ~ r1_setfam_1(X0,X1)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,X1)
       => r1_setfam_1(X0,X1) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_setfam_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_setfam_1)).

fof(f39,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f21,f36])).

fof(f21,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:31:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.43  % (30902)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.19/0.43  % (30894)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.19/0.44  % (30894)Refutation found. Thanks to Tanya!
% 0.19/0.44  % SZS status Theorem for theBenchmark
% 0.19/0.44  % SZS output start Proof for theBenchmark
% 0.19/0.44  fof(f105,plain,(
% 0.19/0.44    $false),
% 0.19/0.44    inference(avatar_sat_refutation,[],[f39,f44,f104])).
% 0.19/0.44  fof(f104,plain,(
% 0.19/0.44    ~spl4_1 | spl4_2),
% 0.19/0.44    inference(avatar_contradiction_clause,[],[f103])).
% 0.19/0.44  fof(f103,plain,(
% 0.19/0.44    $false | (~spl4_1 | spl4_2)),
% 0.19/0.44    inference(subsumption_resolution,[],[f99,f38])).
% 0.19/0.44  fof(f38,plain,(
% 0.19/0.44    r1_tarski(sK0,sK1) | ~spl4_1),
% 0.19/0.44    inference(avatar_component_clause,[],[f36])).
% 0.19/0.44  fof(f36,plain,(
% 0.19/0.44    spl4_1 <=> r1_tarski(sK0,sK1)),
% 0.19/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.19/0.44  fof(f99,plain,(
% 0.19/0.44    ~r1_tarski(sK0,sK1) | spl4_2),
% 0.19/0.44    inference(resolution,[],[f97,f43])).
% 0.19/0.44  fof(f43,plain,(
% 0.19/0.44    ~r1_setfam_1(sK0,sK1) | spl4_2),
% 0.19/0.44    inference(avatar_component_clause,[],[f41])).
% 0.19/0.44  fof(f41,plain,(
% 0.19/0.44    spl4_2 <=> r1_setfam_1(sK0,sK1)),
% 0.19/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.19/0.44  fof(f97,plain,(
% 0.19/0.44    ( ! [X0,X1] : (r1_setfam_1(X0,X1) | ~r1_tarski(X0,X1)) )),
% 0.19/0.44    inference(duplicate_literal_removal,[],[f94])).
% 0.19/0.44  fof(f94,plain,(
% 0.19/0.44    ( ! [X0,X1] : (r1_setfam_1(X0,X1) | ~r1_tarski(X0,X1) | r1_setfam_1(X0,X1)) )),
% 0.19/0.44    inference(resolution,[],[f76,f65])).
% 0.19/0.44  fof(f65,plain,(
% 0.19/0.44    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_setfam_1(X0,X1)) )),
% 0.19/0.44    inference(resolution,[],[f29,f33])).
% 0.19/0.44  fof(f33,plain,(
% 0.19/0.44    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.19/0.44    inference(equality_resolution,[],[f24])).
% 0.19/0.44  fof(f24,plain,(
% 0.19/0.44    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.19/0.44    inference(cnf_transformation,[],[f14])).
% 0.19/0.44  fof(f14,plain,(
% 0.19/0.44    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.19/0.44    inference(flattening,[],[f13])).
% 0.19/0.44  fof(f13,plain,(
% 0.19/0.44    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.19/0.44    inference(nnf_transformation,[],[f1])).
% 0.19/0.44  fof(f1,axiom,(
% 0.19/0.44    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.19/0.44  fof(f29,plain,(
% 0.19/0.44    ( ! [X0,X3,X1] : (~r1_tarski(sK2(X0,X1),X3) | r1_setfam_1(X0,X1) | ~r2_hidden(X3,X1)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f19])).
% 0.19/0.44  fof(f19,plain,(
% 0.19/0.44    ! [X0,X1] : ((r1_setfam_1(X0,X1) | (! [X3] : (~r1_tarski(sK2(X0,X1),X3) | ~r2_hidden(X3,X1)) & r2_hidden(sK2(X0,X1),X0))) & (! [X4] : ((r1_tarski(X4,sK3(X1,X4)) & r2_hidden(sK3(X1,X4),X1)) | ~r2_hidden(X4,X0)) | ~r1_setfam_1(X0,X1)))),
% 0.19/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f16,f18,f17])).
% 0.19/0.44  fof(f17,plain,(
% 0.19/0.44    ! [X1,X0] : (? [X2] : (! [X3] : (~r1_tarski(X2,X3) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X0)) => (! [X3] : (~r1_tarski(sK2(X0,X1),X3) | ~r2_hidden(X3,X1)) & r2_hidden(sK2(X0,X1),X0)))),
% 0.19/0.44    introduced(choice_axiom,[])).
% 0.19/0.44  fof(f18,plain,(
% 0.19/0.44    ! [X4,X1] : (? [X5] : (r1_tarski(X4,X5) & r2_hidden(X5,X1)) => (r1_tarski(X4,sK3(X1,X4)) & r2_hidden(sK3(X1,X4),X1)))),
% 0.19/0.44    introduced(choice_axiom,[])).
% 0.19/0.44  fof(f16,plain,(
% 0.19/0.44    ! [X0,X1] : ((r1_setfam_1(X0,X1) | ? [X2] : (! [X3] : (~r1_tarski(X2,X3) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X0))) & (! [X4] : (? [X5] : (r1_tarski(X4,X5) & r2_hidden(X5,X1)) | ~r2_hidden(X4,X0)) | ~r1_setfam_1(X0,X1)))),
% 0.19/0.44    inference(rectify,[],[f15])).
% 0.19/0.44  fof(f15,plain,(
% 0.19/0.44    ! [X0,X1] : ((r1_setfam_1(X0,X1) | ? [X2] : (! [X3] : (~r1_tarski(X2,X3) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X0))) & (! [X2] : (? [X3] : (r1_tarski(X2,X3) & r2_hidden(X3,X1)) | ~r2_hidden(X2,X0)) | ~r1_setfam_1(X0,X1)))),
% 0.19/0.44    inference(nnf_transformation,[],[f8])).
% 0.19/0.44  fof(f8,plain,(
% 0.19/0.44    ! [X0,X1] : (r1_setfam_1(X0,X1) <=> ! [X2] : (? [X3] : (r1_tarski(X2,X3) & r2_hidden(X3,X1)) | ~r2_hidden(X2,X0)))),
% 0.19/0.44    inference(ennf_transformation,[],[f4])).
% 0.19/0.44  fof(f4,axiom,(
% 0.19/0.44    ! [X0,X1] : (r1_setfam_1(X0,X1) <=> ! [X2] : ~(! [X3] : ~(r1_tarski(X2,X3) & r2_hidden(X3,X1)) & r2_hidden(X2,X0)))),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).
% 0.19/0.44  fof(f76,plain,(
% 0.19/0.44    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X2),X1) | r1_setfam_1(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.19/0.44    inference(resolution,[],[f72,f30])).
% 0.19/0.44  fof(f30,plain,(
% 0.19/0.44    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f20])).
% 0.19/0.44  fof(f20,plain,(
% 0.19/0.44    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.19/0.44    inference(nnf_transformation,[],[f3])).
% 0.19/0.44  fof(f3,axiom,(
% 0.19/0.44    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.19/0.44  fof(f72,plain,(
% 0.19/0.44    ( ! [X4,X2,X3] : (r1_tarski(k1_tarski(sK2(X2,X3)),X4) | ~r1_tarski(X2,X4) | r1_setfam_1(X2,X3)) )),
% 0.19/0.44    inference(resolution,[],[f47,f32])).
% 0.19/0.44  fof(f32,plain,(
% 0.19/0.44    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f10])).
% 0.19/0.44  fof(f10,plain,(
% 0.19/0.44    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.19/0.44    inference(flattening,[],[f9])).
% 0.19/0.44  fof(f9,plain,(
% 0.19/0.44    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.19/0.44    inference(ennf_transformation,[],[f2])).
% 0.19/0.44  fof(f2,axiom,(
% 0.19/0.44    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.19/0.44  fof(f47,plain,(
% 0.19/0.44    ( ! [X0,X1] : (r1_tarski(k1_tarski(sK2(X0,X1)),X0) | r1_setfam_1(X0,X1)) )),
% 0.19/0.44    inference(resolution,[],[f28,f31])).
% 0.19/0.44  fof(f31,plain,(
% 0.19/0.44    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f20])).
% 0.19/0.44  fof(f28,plain,(
% 0.19/0.44    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_setfam_1(X0,X1)) )),
% 0.19/0.44    inference(cnf_transformation,[],[f19])).
% 0.19/0.44  fof(f44,plain,(
% 0.19/0.44    ~spl4_2),
% 0.19/0.44    inference(avatar_split_clause,[],[f22,f41])).
% 0.19/0.44  fof(f22,plain,(
% 0.19/0.44    ~r1_setfam_1(sK0,sK1)),
% 0.19/0.44    inference(cnf_transformation,[],[f12])).
% 0.19/0.44  fof(f12,plain,(
% 0.19/0.44    ~r1_setfam_1(sK0,sK1) & r1_tarski(sK0,sK1)),
% 0.19/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f11])).
% 0.19/0.44  fof(f11,plain,(
% 0.19/0.44    ? [X0,X1] : (~r1_setfam_1(X0,X1) & r1_tarski(X0,X1)) => (~r1_setfam_1(sK0,sK1) & r1_tarski(sK0,sK1))),
% 0.19/0.44    introduced(choice_axiom,[])).
% 0.19/0.44  fof(f7,plain,(
% 0.19/0.44    ? [X0,X1] : (~r1_setfam_1(X0,X1) & r1_tarski(X0,X1))),
% 0.19/0.44    inference(ennf_transformation,[],[f6])).
% 0.19/0.44  fof(f6,negated_conjecture,(
% 0.19/0.44    ~! [X0,X1] : (r1_tarski(X0,X1) => r1_setfam_1(X0,X1))),
% 0.19/0.44    inference(negated_conjecture,[],[f5])).
% 0.19/0.44  fof(f5,conjecture,(
% 0.19/0.44    ! [X0,X1] : (r1_tarski(X0,X1) => r1_setfam_1(X0,X1))),
% 0.19/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_setfam_1)).
% 0.19/0.44  fof(f39,plain,(
% 0.19/0.44    spl4_1),
% 0.19/0.44    inference(avatar_split_clause,[],[f21,f36])).
% 0.19/0.44  fof(f21,plain,(
% 0.19/0.44    r1_tarski(sK0,sK1)),
% 0.19/0.44    inference(cnf_transformation,[],[f12])).
% 0.19/0.44  % SZS output end Proof for theBenchmark
% 0.19/0.44  % (30894)------------------------------
% 0.19/0.44  % (30894)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.44  % (30894)Termination reason: Refutation
% 0.19/0.44  
% 0.19/0.44  % (30894)Memory used [KB]: 6140
% 0.19/0.44  % (30894)Time elapsed: 0.052 s
% 0.19/0.44  % (30894)------------------------------
% 0.19/0.44  % (30894)------------------------------
% 0.19/0.44  % (30887)Success in time 0.089 s
%------------------------------------------------------------------------------
