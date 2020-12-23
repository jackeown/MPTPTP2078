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
% DateTime   : Thu Dec  3 12:58:11 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 165 expanded)
%              Number of leaves         :   12 (  51 expanded)
%              Depth                    :   12
%              Number of atoms          :  167 ( 569 expanded)
%              Number of equality atoms :   25 (  57 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f214,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f111,f119,f165,f213])).

fof(f213,plain,
    ( ~ spl3_3
    | ~ spl3_7 ),
    inference(avatar_contradiction_clause,[],[f209])).

fof(f209,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(resolution,[],[f190,f62])).

fof(f62,plain,
    ( r1_xboole_0(sK1(sK0,sK0),sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl3_3
  <=> r1_xboole_0(sK1(sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f190,plain,
    ( ~ r1_xboole_0(sK1(sK0,sK0),sK0)
    | ~ spl3_7 ),
    inference(resolution,[],[f188,f20])).

fof(f20,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | ~ r1_xboole_0(X1,sK0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(X1,sK0)
        | ~ r2_hidden(X1,sK0) )
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f12])).

fof(f12,plain,
    ( ? [X0] :
        ( ! [X1] :
            ( ~ r1_xboole_0(X1,X0)
            | ~ r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 )
   => ( ! [X1] :
          ( ~ r1_xboole_0(X1,sK0)
          | ~ r2_hidden(X1,sK0) )
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ~ r1_xboole_0(X1,X0)
          | ~ r2_hidden(X1,X0) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ~ ( ! [X1] :
              ~ ( r1_xboole_0(X1,X0)
                & r2_hidden(X1,X0) )
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( r1_xboole_0(X1,X0)
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).

fof(f188,plain,
    ( r2_hidden(sK1(sK0,sK0),sK0)
    | ~ spl3_7 ),
    inference(resolution,[],[f186,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f10,f14])).

fof(f14,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

% (28587)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
fof(f186,plain,
    ( ~ r1_xboole_0(sK0,sK0)
    | ~ spl3_7 ),
    inference(resolution,[],[f170,f168])).

fof(f168,plain,
    ( r2_hidden(sK2(sK0),sK0)
    | ~ spl3_7 ),
    inference(resolution,[],[f164,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(sK2(X1),X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK2(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK2(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f11,f17])).

fof(f17,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,sK2(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK2(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

fof(f164,plain,
    ( r2_hidden(sK1(sK0,k4_xboole_0(sK0,sK0)),sK0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl3_7
  <=> r2_hidden(sK1(sK0,k4_xboole_0(sK0,sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f170,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2(sK0),X0)
        | ~ r1_xboole_0(X0,sK0) )
    | ~ spl3_7 ),
    inference(resolution,[],[f168,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f165,plain,
    ( spl3_7
    | spl3_4
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f157,f61,f65,f162])).

% (28607)Refutation not found, incomplete strategy% (28607)------------------------------
% (28607)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (28607)Termination reason: Refutation not found, incomplete strategy

% (28607)Memory used [KB]: 10618
% (28607)Time elapsed: 0.116 s
% (28607)------------------------------
% (28607)------------------------------
fof(f65,plain,
    ( spl3_4
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f157,plain,
    ( k1_xboole_0 = sK0
    | r2_hidden(sK1(sK0,k4_xboole_0(sK0,sK0)),sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f138,f62])).

fof(f138,plain,(
    ! [X2] :
      ( ~ r1_xboole_0(sK1(X2,sK0),sK0)
      | k1_xboole_0 = X2
      | r2_hidden(sK1(X2,k4_xboole_0(X2,sK0)),X2) ) ),
    inference(resolution,[],[f94,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f94,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,k4_xboole_0(X0,sK0))
      | k1_xboole_0 = X0
      | ~ r1_xboole_0(sK1(X0,sK0),sK0) ) ),
    inference(resolution,[],[f73,f20])).

fof(f73,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK1(X2,X3),X3)
      | k1_xboole_0 = X2
      | ~ r1_xboole_0(X2,k4_xboole_0(X2,X3)) ) ),
    inference(resolution,[],[f35,f24])).

fof(f35,plain,(
    ! [X2,X1] :
      ( ~ r1_xboole_0(X1,X2)
      | ~ r1_xboole_0(X1,k4_xboole_0(X1,X2))
      | k1_xboole_0 = X1 ) ),
    inference(forward_demodulation,[],[f34,f21])).

fof(f21,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f34,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k4_xboole_0(X1,k1_xboole_0)
      | ~ r1_xboole_0(X1,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X1,X2) ) ),
    inference(superposition,[],[f31,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f26,f22])).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f119,plain,(
    ~ spl3_4 ),
    inference(avatar_contradiction_clause,[],[f118])).

fof(f118,plain,
    ( $false
    | ~ spl3_4 ),
    inference(trivial_inequality_removal,[],[f117])).

fof(f117,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl3_4 ),
    inference(superposition,[],[f19,f67])).

fof(f67,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f65])).

fof(f19,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f13])).

fof(f111,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f109])).

fof(f109,plain,
    ( $false
    | spl3_3 ),
    inference(resolution,[],[f106,f82])).

fof(f82,plain,
    ( r2_hidden(sK1(sK2(sK0),sK0),sK0)
    | spl3_3 ),
    inference(resolution,[],[f78,f24])).

fof(f78,plain,
    ( ~ r1_xboole_0(sK2(sK0),sK0)
    | spl3_3 ),
    inference(resolution,[],[f77,f20])).

fof(f77,plain,
    ( r2_hidden(sK2(sK0),sK0)
    | spl3_3 ),
    inference(resolution,[],[f70,f28])).

fof(f70,plain,
    ( r2_hidden(sK1(sK1(sK0,sK0),sK0),sK0)
    | spl3_3 ),
    inference(resolution,[],[f63,f24])).

fof(f63,plain,
    ( ~ r1_xboole_0(sK1(sK0,sK0),sK0)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f61])).

fof(f106,plain,
    ( ~ r2_hidden(sK1(sK2(sK0),sK0),sK0)
    | spl3_3 ),
    inference(resolution,[],[f83,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK2(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(condensation,[],[f29])).

fof(f29,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,sK2(X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f83,plain,
    ( r2_hidden(sK1(sK2(sK0),sK0),sK2(sK0))
    | spl3_3 ),
    inference(resolution,[],[f78,f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:46:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (28607)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.50  % (28585)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (28591)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (28591)Refutation not found, incomplete strategy% (28591)------------------------------
% 0.21/0.51  % (28591)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (28599)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (28591)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (28591)Memory used [KB]: 6140
% 0.21/0.51  % (28591)Time elapsed: 0.102 s
% 0.21/0.51  % (28591)------------------------------
% 0.21/0.51  % (28591)------------------------------
% 0.21/0.52  % (28598)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (28599)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (28590)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f214,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f111,f119,f165,f213])).
% 0.21/0.52  fof(f213,plain,(
% 0.21/0.52    ~spl3_3 | ~spl3_7),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f209])).
% 0.21/0.52  fof(f209,plain,(
% 0.21/0.52    $false | (~spl3_3 | ~spl3_7)),
% 0.21/0.52    inference(resolution,[],[f190,f62])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    r1_xboole_0(sK1(sK0,sK0),sK0) | ~spl3_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f61])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    spl3_3 <=> r1_xboole_0(sK1(sK0,sK0),sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.52  fof(f190,plain,(
% 0.21/0.52    ~r1_xboole_0(sK1(sK0,sK0),sK0) | ~spl3_7),
% 0.21/0.52    inference(resolution,[],[f188,f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ( ! [X1] : (~r2_hidden(X1,sK0) | ~r1_xboole_0(X1,sK0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ! [X1] : (~r1_xboole_0(X1,sK0) | ~r2_hidden(X1,sK0)) & k1_xboole_0 != sK0),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ? [X0] : (! [X1] : (~r1_xboole_0(X1,X0) | ~r2_hidden(X1,X0)) & k1_xboole_0 != X0) => (! [X1] : (~r1_xboole_0(X1,sK0) | ~r2_hidden(X1,sK0)) & k1_xboole_0 != sK0)),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    ? [X0] : (! [X1] : (~r1_xboole_0(X1,X0) | ~r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,negated_conjecture,(
% 0.21/0.52    ~! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.52    inference(negated_conjecture,[],[f6])).
% 0.21/0.52  fof(f6,conjecture,(
% 0.21/0.52    ! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).
% 0.21/0.52  fof(f188,plain,(
% 0.21/0.52    r2_hidden(sK1(sK0,sK0),sK0) | ~spl3_7),
% 0.21/0.52    inference(resolution,[],[f186,f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f10,f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,plain,(
% 0.21/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.52    inference(rectify,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.52  % (28587)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  fof(f186,plain,(
% 0.21/0.52    ~r1_xboole_0(sK0,sK0) | ~spl3_7),
% 0.21/0.52    inference(resolution,[],[f170,f168])).
% 0.21/0.52  fof(f168,plain,(
% 0.21/0.52    r2_hidden(sK2(sK0),sK0) | ~spl3_7),
% 0.21/0.52    inference(resolution,[],[f164,f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r2_hidden(sK2(X1),X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0,X1] : ((! [X3] : (~r2_hidden(X3,sK2(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK2(X1),X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f11,f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) => (! [X3] : (~r2_hidden(X3,sK2(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK2(X1),X1)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1] : ~(! [X2] : ~(! [X3] : ~(r2_hidden(X3,X2) & r2_hidden(X3,X1)) & r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).
% 0.21/0.52  fof(f164,plain,(
% 0.21/0.52    r2_hidden(sK1(sK0,k4_xboole_0(sK0,sK0)),sK0) | ~spl3_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f162])).
% 0.21/0.52  fof(f162,plain,(
% 0.21/0.52    spl3_7 <=> r2_hidden(sK1(sK0,k4_xboole_0(sK0,sK0)),sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.52  fof(f170,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(sK2(sK0),X0) | ~r1_xboole_0(X0,sK0)) ) | ~spl3_7),
% 0.21/0.52    inference(resolution,[],[f168,f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f165,plain,(
% 0.21/0.52    spl3_7 | spl3_4 | ~spl3_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f157,f61,f65,f162])).
% 0.21/0.52  % (28607)Refutation not found, incomplete strategy% (28607)------------------------------
% 0.21/0.52  % (28607)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (28607)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (28607)Memory used [KB]: 10618
% 0.21/0.52  % (28607)Time elapsed: 0.116 s
% 0.21/0.52  % (28607)------------------------------
% 0.21/0.52  % (28607)------------------------------
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    spl3_4 <=> k1_xboole_0 = sK0),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.52  fof(f157,plain,(
% 0.21/0.52    k1_xboole_0 = sK0 | r2_hidden(sK1(sK0,k4_xboole_0(sK0,sK0)),sK0) | ~spl3_3),
% 0.21/0.52    inference(resolution,[],[f138,f62])).
% 0.21/0.52  fof(f138,plain,(
% 0.21/0.52    ( ! [X2] : (~r1_xboole_0(sK1(X2,sK0),sK0) | k1_xboole_0 = X2 | r2_hidden(sK1(X2,k4_xboole_0(X2,sK0)),X2)) )),
% 0.21/0.52    inference(resolution,[],[f94,f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f94,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_xboole_0(X0,k4_xboole_0(X0,sK0)) | k1_xboole_0 = X0 | ~r1_xboole_0(sK1(X0,sK0),sK0)) )),
% 0.21/0.52    inference(resolution,[],[f73,f20])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    ( ! [X2,X3] : (r2_hidden(sK1(X2,X3),X3) | k1_xboole_0 = X2 | ~r1_xboole_0(X2,k4_xboole_0(X2,X3))) )),
% 0.21/0.52    inference(resolution,[],[f35,f24])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ( ! [X2,X1] : (~r1_xboole_0(X1,X2) | ~r1_xboole_0(X1,k4_xboole_0(X1,X2)) | k1_xboole_0 = X1) )),
% 0.21/0.52    inference(forward_demodulation,[],[f34,f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,k1_xboole_0) | ~r1_xboole_0(X1,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X1,X2)) )),
% 0.21/0.52    inference(superposition,[],[f31,f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f26,f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.52    inference(nnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.52  fof(f119,plain,(
% 0.21/0.52    ~spl3_4),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f118])).
% 0.21/0.52  fof(f118,plain,(
% 0.21/0.52    $false | ~spl3_4),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f117])).
% 0.21/0.52  fof(f117,plain,(
% 0.21/0.52    k1_xboole_0 != k1_xboole_0 | ~spl3_4),
% 0.21/0.52    inference(superposition,[],[f19,f67])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    k1_xboole_0 = sK0 | ~spl3_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f65])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    k1_xboole_0 != sK0),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f111,plain,(
% 0.21/0.52    spl3_3),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f109])).
% 0.21/0.52  fof(f109,plain,(
% 0.21/0.52    $false | spl3_3),
% 0.21/0.52    inference(resolution,[],[f106,f82])).
% 0.21/0.52  fof(f82,plain,(
% 0.21/0.52    r2_hidden(sK1(sK2(sK0),sK0),sK0) | spl3_3),
% 0.21/0.52    inference(resolution,[],[f78,f24])).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    ~r1_xboole_0(sK2(sK0),sK0) | spl3_3),
% 0.21/0.52    inference(resolution,[],[f77,f20])).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    r2_hidden(sK2(sK0),sK0) | spl3_3),
% 0.21/0.52    inference(resolution,[],[f70,f28])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    r2_hidden(sK1(sK1(sK0,sK0),sK0),sK0) | spl3_3),
% 0.21/0.52    inference(resolution,[],[f63,f24])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    ~r1_xboole_0(sK1(sK0,sK0),sK0) | spl3_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f61])).
% 0.21/0.52  fof(f106,plain,(
% 0.21/0.52    ~r2_hidden(sK1(sK2(sK0),sK0),sK0) | spl3_3),
% 0.21/0.52    inference(resolution,[],[f83,f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X0,sK2(X1)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.52    inference(condensation,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (~r2_hidden(X3,sK2(X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    r2_hidden(sK1(sK2(sK0),sK0),sK2(sK0)) | spl3_3),
% 0.21/0.52    inference(resolution,[],[f78,f23])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (28599)------------------------------
% 0.21/0.52  % (28599)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (28599)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (28599)Memory used [KB]: 6268
% 0.21/0.52  % (28599)Time elapsed: 0.123 s
% 0.21/0.52  % (28599)------------------------------
% 0.21/0.52  % (28599)------------------------------
% 0.21/0.52  % (28585)Refutation not found, incomplete strategy% (28585)------------------------------
% 0.21/0.52  % (28585)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (28585)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (28585)Memory used [KB]: 1663
% 0.21/0.52  % (28585)Time elapsed: 0.114 s
% 0.21/0.52  % (28585)------------------------------
% 0.21/0.52  % (28585)------------------------------
% 0.21/0.53  % (28583)Success in time 0.165 s
%------------------------------------------------------------------------------
