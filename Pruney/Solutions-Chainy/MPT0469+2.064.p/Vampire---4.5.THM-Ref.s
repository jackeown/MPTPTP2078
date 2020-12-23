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
% DateTime   : Thu Dec  3 12:47:42 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 100 expanded)
%              Number of leaves         :   17 (  39 expanded)
%              Depth                    :    8
%              Number of atoms          :  179 ( 306 expanded)
%              Number of equality atoms :   29 (  60 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1042,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f67,f434,f551,f1041])).

fof(f1041,plain,
    ( spl10_2
    | ~ spl10_3
    | ~ spl10_7 ),
    inference(avatar_contradiction_clause,[],[f1040])).

fof(f1040,plain,
    ( $false
    | spl10_2
    | ~ spl10_3
    | ~ spl10_7 ),
    inference(subsumption_resolution,[],[f1030,f550])).

fof(f550,plain,
    ( sP0(k1_xboole_0,k2_relat_1(k1_xboole_0))
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f548])).

fof(f548,plain,
    ( spl10_7
  <=> sP0(k1_xboole_0,k2_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f1030,plain,
    ( ~ sP0(k1_xboole_0,k2_relat_1(k1_xboole_0))
    | spl10_2
    | ~ spl10_3 ),
    inference(unit_resulting_resolution,[],[f56,f65,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X2)
      | X1 = X2
      | ~ sP0(X0,X1) ) ),
    inference(superposition,[],[f34,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ~ sP0(X0,X1) )
      & ( sP0(X0,X1)
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> sP0(X0,X1) ) ),
    inference(definition_folding,[],[f3,f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f65,plain,
    ( sP0(k1_xboole_0,k1_xboole_0)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl10_3
  <=> sP0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f56,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | spl10_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl10_2
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f551,plain,(
    spl10_7 ),
    inference(avatar_split_clause,[],[f248,f548])).

fof(f248,plain,(
    sP0(k1_xboole_0,k2_relat_1(k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f117,f86,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
      | sP0(X0,X1)
      | r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK2(X0,X1),X3),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f13,f16,f15,f14])).

fof(f14,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK2(X0,X1),X3),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK2(X0,X1),X4),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK2(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f86,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f28,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) != X0
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f28,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f117,plain,(
    ! [X0] : ~ r2_hidden(X0,k2_relat_1(k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f44,f86,f35])).

fof(f35,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK7(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0)
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0)
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK7(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | ~ sP1(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f20,f23,f22,f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0)
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0)
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | ~ sP1(X0,X1) ) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | ~ sP1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f44,plain,(
    ! [X0] : sP1(X0,k2_relat_1(X0)) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ~ sP1(X0,X1) )
      & ( sP1(X0,X1)
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> sP1(X0,X1) ) ),
    inference(definition_folding,[],[f4,f10])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f434,plain,(
    spl10_3 ),
    inference(avatar_split_clause,[],[f240,f64])).

fof(f240,plain,(
    sP0(k1_xboole_0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f86,f86,f31])).

fof(f67,plain,
    ( ~ spl10_3
    | spl10_1 ),
    inference(avatar_split_clause,[],[f59,f50,f64])).

fof(f50,plain,
    ( spl10_1
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f59,plain,
    ( ~ sP0(k1_xboole_0,k1_xboole_0)
    | spl10_1 ),
    inference(unit_resulting_resolution,[],[f52,f34])).

fof(f52,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | spl10_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f57,plain,
    ( ~ spl10_1
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f27,f54,f50])).

fof(f27,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
      & k1_xboole_0 = k1_relat_1(k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:14:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.42  % (15591)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.42  % (15591)Refutation not found, incomplete strategy% (15591)------------------------------
% 0.20/0.42  % (15591)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (15591)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.42  
% 0.20/0.42  % (15591)Memory used [KB]: 6140
% 0.20/0.42  % (15591)Time elapsed: 0.027 s
% 0.20/0.42  % (15591)------------------------------
% 0.20/0.42  % (15591)------------------------------
% 0.20/0.44  % (15592)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.45  % (15592)Refutation found. Thanks to Tanya!
% 0.20/0.45  % SZS status Theorem for theBenchmark
% 0.20/0.45  % SZS output start Proof for theBenchmark
% 0.20/0.45  fof(f1042,plain,(
% 0.20/0.45    $false),
% 0.20/0.45    inference(avatar_sat_refutation,[],[f57,f67,f434,f551,f1041])).
% 0.20/0.45  fof(f1041,plain,(
% 0.20/0.45    spl10_2 | ~spl10_3 | ~spl10_7),
% 0.20/0.45    inference(avatar_contradiction_clause,[],[f1040])).
% 0.20/0.45  fof(f1040,plain,(
% 0.20/0.45    $false | (spl10_2 | ~spl10_3 | ~spl10_7)),
% 0.20/0.45    inference(subsumption_resolution,[],[f1030,f550])).
% 0.20/0.45  fof(f550,plain,(
% 0.20/0.45    sP0(k1_xboole_0,k2_relat_1(k1_xboole_0)) | ~spl10_7),
% 0.20/0.45    inference(avatar_component_clause,[],[f548])).
% 0.20/0.45  fof(f548,plain,(
% 0.20/0.45    spl10_7 <=> sP0(k1_xboole_0,k2_relat_1(k1_xboole_0))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 0.20/0.45  fof(f1030,plain,(
% 0.20/0.45    ~sP0(k1_xboole_0,k2_relat_1(k1_xboole_0)) | (spl10_2 | ~spl10_3)),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f56,f65,f60])).
% 0.20/0.45  fof(f60,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~sP0(X0,X2) | X1 = X2 | ~sP0(X0,X1)) )),
% 0.20/0.45    inference(superposition,[],[f34,f34])).
% 0.20/0.45  fof(f34,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k1_relat_1(X0) = X1 | ~sP0(X0,X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f18])).
% 0.20/0.45  fof(f18,plain,(
% 0.20/0.45    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ~sP0(X0,X1)) & (sP0(X0,X1) | k1_relat_1(X0) != X1))),
% 0.20/0.45    inference(nnf_transformation,[],[f9])).
% 0.20/0.45  fof(f9,plain,(
% 0.20/0.45    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> sP0(X0,X1))),
% 0.20/0.45    inference(definition_folding,[],[f3,f8])).
% 0.20/0.45  fof(f8,plain,(
% 0.20/0.45    ! [X0,X1] : (sP0(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.20/0.45    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.45  fof(f3,axiom,(
% 0.20/0.45    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 0.20/0.45  fof(f65,plain,(
% 0.20/0.45    sP0(k1_xboole_0,k1_xboole_0) | ~spl10_3),
% 0.20/0.45    inference(avatar_component_clause,[],[f64])).
% 0.20/0.45  fof(f64,plain,(
% 0.20/0.45    spl10_3 <=> sP0(k1_xboole_0,k1_xboole_0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 0.20/0.45  fof(f56,plain,(
% 0.20/0.45    k1_xboole_0 != k2_relat_1(k1_xboole_0) | spl10_2),
% 0.20/0.45    inference(avatar_component_clause,[],[f54])).
% 0.20/0.45  fof(f54,plain,(
% 0.20/0.45    spl10_2 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.20/0.45  fof(f551,plain,(
% 0.20/0.45    spl10_7),
% 0.20/0.45    inference(avatar_split_clause,[],[f248,f548])).
% 0.20/0.45  fof(f248,plain,(
% 0.20/0.45    sP0(k1_xboole_0,k2_relat_1(k1_xboole_0))),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f117,f86,f31])).
% 0.20/0.45  fof(f31,plain,(
% 0.20/0.45    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) | sP0(X0,X1) | r2_hidden(sK2(X0,X1),X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f17])).
% 0.20/0.45  fof(f17,plain,(
% 0.20/0.45    ! [X0,X1] : ((sP0(X0,X1) | ((! [X3] : ~r2_hidden(k4_tarski(sK2(X0,X1),X3),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) | ~r2_hidden(X5,X1))) | ~sP0(X0,X1)))),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f13,f16,f15,f14])).
% 0.20/0.45  fof(f14,plain,(
% 0.20/0.45    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK2(X0,X1),X3),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK2(X0,X1),X4),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f15,plain,(
% 0.20/0.45    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK2(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f16,plain,(
% 0.20/0.45    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f13,plain,(
% 0.20/0.45    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | ~sP0(X0,X1)))),
% 0.20/0.45    inference(rectify,[],[f12])).
% 0.20/0.45  fof(f12,plain,(
% 0.20/0.45    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | ~sP0(X0,X1)))),
% 0.20/0.45    inference(nnf_transformation,[],[f8])).
% 0.20/0.45  fof(f86,plain,(
% 0.20/0.45    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f28,f41])).
% 0.20/0.45  fof(f41,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) != X0 | ~r2_hidden(X1,X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f26])).
% 0.20/0.45  fof(f26,plain,(
% 0.20/0.45    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 0.20/0.45    inference(nnf_transformation,[],[f2])).
% 0.20/0.45  fof(f2,axiom,(
% 0.20/0.45    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.20/0.45  fof(f28,plain,(
% 0.20/0.45    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f1])).
% 0.20/0.45  fof(f1,axiom,(
% 0.20/0.45    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 0.20/0.45  fof(f117,plain,(
% 0.20/0.45    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(k1_xboole_0))) )),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f44,f86,f35])).
% 0.20/0.45  fof(f35,plain,(
% 0.20/0.45    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | ~sP1(X0,X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f24])).
% 0.20/0.45  fof(f24,plain,(
% 0.20/0.45    ! [X0,X1] : ((sP1(X0,X1) | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK7(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | ~sP1(X0,X1)))),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f20,f23,f22,f21])).
% 0.20/0.45  fof(f21,plain,(
% 0.20/0.45    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK5(X0,X1)),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1))))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f22,plain,(
% 0.20/0.45    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK5(X0,X1)),X0) => r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f23,plain,(
% 0.20/0.45    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK7(X0,X5),X5),X0))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f20,plain,(
% 0.20/0.45    ! [X0,X1] : ((sP1(X0,X1) | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | ~sP1(X0,X1)))),
% 0.20/0.45    inference(rectify,[],[f19])).
% 0.20/0.45  fof(f19,plain,(
% 0.20/0.45    ! [X0,X1] : ((sP1(X0,X1) | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | ~sP1(X0,X1)))),
% 0.20/0.45    inference(nnf_transformation,[],[f10])).
% 0.20/0.45  fof(f10,plain,(
% 0.20/0.45    ! [X0,X1] : (sP1(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.20/0.45    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.45  fof(f44,plain,(
% 0.20/0.45    ( ! [X0] : (sP1(X0,k2_relat_1(X0))) )),
% 0.20/0.45    inference(equality_resolution,[],[f39])).
% 0.20/0.45  fof(f39,plain,(
% 0.20/0.45    ( ! [X0,X1] : (sP1(X0,X1) | k2_relat_1(X0) != X1) )),
% 0.20/0.45    inference(cnf_transformation,[],[f25])).
% 0.20/0.45  fof(f25,plain,(
% 0.20/0.45    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ~sP1(X0,X1)) & (sP1(X0,X1) | k2_relat_1(X0) != X1))),
% 0.20/0.45    inference(nnf_transformation,[],[f11])).
% 0.20/0.45  fof(f11,plain,(
% 0.20/0.45    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> sP1(X0,X1))),
% 0.20/0.45    inference(definition_folding,[],[f4,f10])).
% 0.20/0.45  fof(f4,axiom,(
% 0.20/0.45    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 0.20/0.45  fof(f434,plain,(
% 0.20/0.45    spl10_3),
% 0.20/0.45    inference(avatar_split_clause,[],[f240,f64])).
% 0.20/0.45  fof(f240,plain,(
% 0.20/0.45    sP0(k1_xboole_0,k1_xboole_0)),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f86,f86,f31])).
% 0.20/0.45  fof(f67,plain,(
% 0.20/0.45    ~spl10_3 | spl10_1),
% 0.20/0.45    inference(avatar_split_clause,[],[f59,f50,f64])).
% 0.20/0.45  fof(f50,plain,(
% 0.20/0.45    spl10_1 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.20/0.45  fof(f59,plain,(
% 0.20/0.45    ~sP0(k1_xboole_0,k1_xboole_0) | spl10_1),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f52,f34])).
% 0.20/0.45  fof(f52,plain,(
% 0.20/0.45    k1_xboole_0 != k1_relat_1(k1_xboole_0) | spl10_1),
% 0.20/0.45    inference(avatar_component_clause,[],[f50])).
% 0.20/0.45  fof(f57,plain,(
% 0.20/0.45    ~spl10_1 | ~spl10_2),
% 0.20/0.45    inference(avatar_split_clause,[],[f27,f54,f50])).
% 0.20/0.45  fof(f27,plain,(
% 0.20/0.45    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 0.20/0.45    inference(cnf_transformation,[],[f7])).
% 0.20/0.45  fof(f7,plain,(
% 0.20/0.45    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 0.20/0.45    inference(ennf_transformation,[],[f6])).
% 0.20/0.45  fof(f6,negated_conjecture,(
% 0.20/0.45    ~(k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0))),
% 0.20/0.45    inference(negated_conjecture,[],[f5])).
% 0.20/0.45  fof(f5,conjecture,(
% 0.20/0.45    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.45  % SZS output end Proof for theBenchmark
% 0.20/0.45  % (15592)------------------------------
% 0.20/0.45  % (15592)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (15592)Termination reason: Refutation
% 0.20/0.45  
% 0.20/0.45  % (15592)Memory used [KB]: 11129
% 0.20/0.45  % (15592)Time elapsed: 0.058 s
% 0.20/0.45  % (15592)------------------------------
% 0.20/0.45  % (15592)------------------------------
% 0.20/0.45  % (15575)Success in time 0.099 s
%------------------------------------------------------------------------------
