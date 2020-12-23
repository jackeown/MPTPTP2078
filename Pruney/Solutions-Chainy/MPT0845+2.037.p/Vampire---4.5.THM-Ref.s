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
% DateTime   : Thu Dec  3 12:58:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 120 expanded)
%              Number of leaves         :   15 (  38 expanded)
%              Depth                    :   11
%              Number of atoms          :  222 ( 437 expanded)
%              Number of equality atoms :   35 (  47 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f566,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f133,f565])).

fof(f565,plain,
    ( spl7_1
    | spl7_5 ),
    inference(avatar_contradiction_clause,[],[f564])).

fof(f564,plain,
    ( $false
    | spl7_1
    | spl7_5 ),
    inference(subsumption_resolution,[],[f563,f59])).

fof(f59,plain,
    ( k1_xboole_0 != sK2
    | spl7_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl7_1
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f563,plain,
    ( k1_xboole_0 = sK2
    | spl7_5 ),
    inference(forward_demodulation,[],[f556,f494])).

fof(f494,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(sK2,X0)
    | spl7_5 ),
    inference(unit_resulting_resolution,[],[f474,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ~ sP1(X0,X1,X2) )
      & ( sP1(X0,X1,X2)
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> sP1(X0,X1,X2) ) ),
    inference(definition_folding,[],[f1,f13,f12])).

fof(f12,plain,(
    ! [X1,X3,X0] :
      ( sP0(X1,X3,X0)
    <=> ( ~ r2_hidden(X3,X1)
        & r2_hidden(X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP0(X1,X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f474,plain,
    ( ! [X0] : sP1(sK2,X0,k1_xboole_0)
    | spl7_5 ),
    inference(unit_resulting_resolution,[],[f61,f153,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,sK5(X0,X1,X2),X0)
      | sP1(X0,X1,X2)
      | r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ~ sP0(X1,sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( sP0(X1,sK5(X0,X1,X2),X0)
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X1,X4,X0) )
            & ( sP0(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f24,f25])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP0(X1,X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP0(X1,X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP0(X1,sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( sP0(X1,sK5(X0,X1,X2),X0)
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X1,X4,X0) )
            & ( sP0(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP0(X1,X3,X0) )
            & ( sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f13])).

% (23396)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
fof(f153,plain,
    ( ! [X0,X1] : ~ sP0(X0,X1,sK2)
    | spl7_5 ),
    inference(unit_resulting_resolution,[],[f134,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | r2_hidden(X1,X0)
        | ~ r2_hidden(X1,X2) )
      & ( ( ~ r2_hidden(X1,X0)
          & r2_hidden(X1,X2) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X1,X3,X0] :
      ( ( sP0(X1,X3,X0)
        | r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( ~ r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP0(X1,X3,X0) ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X1,X3,X0] :
      ( ( sP0(X1,X3,X0)
        | r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( ~ r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP0(X1,X3,X0) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f134,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2)
    | spl7_5 ),
    inference(unit_resulting_resolution,[],[f131,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X1),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK4(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK4(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f11,f21])).

fof(f21,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,sK4(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK4(X1),X1) ) ) ),
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

fof(f131,plain,
    ( ~ r2_hidden(sK4(sK2),sK2)
    | spl7_5 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl7_5
  <=> r2_hidden(sK4(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f61,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f33,f51])).

fof(f51,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f33,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f556,plain,
    ( ! [X0] : sK2 = k4_xboole_0(sK2,X0)
    | spl7_5 ),
    inference(unit_resulting_resolution,[],[f475,f50])).

fof(f475,plain,
    ( ! [X0] : sP1(sK2,X0,sK2)
    | spl7_5 ),
    inference(unit_resulting_resolution,[],[f134,f153,f44])).

fof(f133,plain,(
    ~ spl7_5 ),
    inference(avatar_split_clause,[],[f126,f129])).

fof(f126,plain,(
    ~ r2_hidden(sK4(sK2),sK2) ),
    inference(resolution,[],[f124,f32])).

fof(f32,plain,(
    ! [X1] :
      ( ~ r1_xboole_0(X1,sK2)
      | ~ r2_hidden(X1,sK2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(X1,sK2)
        | ~ r2_hidden(X1,sK2) )
    & k1_xboole_0 != sK2 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f9,f15])).

fof(f15,plain,
    ( ? [X0] :
        ( ! [X1] :
            ( ~ r1_xboole_0(X1,X0)
            | ~ r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 )
   => ( ! [X1] :
          ( ~ r1_xboole_0(X1,sK2)
          | ~ r2_hidden(X1,sK2) )
      & k1_xboole_0 != sK2 ) ),
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

fof(f124,plain,(
    ! [X0] : r1_xboole_0(sK4(X0),X0) ),
    inference(duplicate_literal_removal,[],[f123])).

fof(f123,plain,(
    ! [X0] :
      ( r1_xboole_0(sK4(X0),X0)
      | r1_xboole_0(sK4(X0),X0) ) ),
    inference(resolution,[],[f109,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f10,f17])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
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

fof(f109,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(sK3(sK4(X2),X3),X2)
      | r1_xboole_0(sK4(X2),X3) ) ),
    inference(subsumption_resolution,[],[f106,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | sP6(X1) ) ),
    inference(cnf_transformation,[],[f54_D])).

fof(f54_D,plain,(
    ! [X1] :
      ( ! [X0] : ~ r2_hidden(X0,X1)
    <=> ~ sP6(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).

fof(f106,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(sK3(sK4(X2),X3),X2)
      | ~ sP6(X2)
      | r1_xboole_0(sK4(X2),X3) ) ),
    inference(resolution,[],[f55,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f55,plain,(
    ! [X3,X1] :
      ( ~ r2_hidden(X3,sK4(X1))
      | ~ r2_hidden(X3,X1)
      | ~ sP6(X1) ) ),
    inference(general_splitting,[],[f41,f54_D])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,sK4(X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

% (23396)Refutation not found, incomplete strategy% (23396)------------------------------
% (23396)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (23396)Termination reason: Refutation not found, incomplete strategy

% (23396)Memory used [KB]: 6140
% (23396)Time elapsed: 0.061 s
% (23396)------------------------------
% (23396)------------------------------
fof(f60,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f31,f57])).

fof(f31,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f16])).
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
% 0.14/0.34  % DateTime   : Tue Dec  1 11:05:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.42  % (23416)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.42  % (23416)Refutation not found, incomplete strategy% (23416)------------------------------
% 0.21/0.42  % (23416)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (23416)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.42  
% 0.21/0.42  % (23416)Memory used [KB]: 10490
% 0.21/0.42  % (23416)Time elapsed: 0.003 s
% 0.21/0.42  % (23416)------------------------------
% 0.21/0.42  % (23416)------------------------------
% 0.21/0.46  % (23412)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.47  % (23412)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f566,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f60,f133,f565])).
% 0.21/0.47  fof(f565,plain,(
% 0.21/0.47    spl7_1 | spl7_5),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f564])).
% 0.21/0.47  fof(f564,plain,(
% 0.21/0.47    $false | (spl7_1 | spl7_5)),
% 0.21/0.47    inference(subsumption_resolution,[],[f563,f59])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    k1_xboole_0 != sK2 | spl7_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f57])).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    spl7_1 <=> k1_xboole_0 = sK2),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.47  fof(f563,plain,(
% 0.21/0.47    k1_xboole_0 = sK2 | spl7_5),
% 0.21/0.47    inference(forward_demodulation,[],[f556,f494])).
% 0.21/0.47  fof(f494,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(sK2,X0)) ) | spl7_5),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f474,f50])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~sP1(X0,X1,X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f30])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ~sP1(X0,X1,X2)) & (sP1(X0,X1,X2) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.47    inference(nnf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> sP1(X0,X1,X2))),
% 0.21/0.47    inference(definition_folding,[],[f1,f13,f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X1,X3,X0] : (sP0(X1,X3,X0) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0)))),
% 0.21/0.47    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (sP1(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP0(X1,X3,X0)))),
% 0.21/0.47    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.21/0.47  fof(f474,plain,(
% 0.21/0.47    ( ! [X0] : (sP1(sK2,X0,k1_xboole_0)) ) | spl7_5),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f61,f153,f44])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (sP0(X1,sK5(X0,X1,X2),X0) | sP1(X0,X1,X2) | r2_hidden(sK5(X0,X1,X2),X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ((~sP0(X1,sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sP0(X1,sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X1,X4,X0)) & (sP0(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f24,f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ! [X2,X1,X0] : (? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2))) => ((~sP0(X1,sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sP0(X1,sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X1,X4,X0)) & (sP0(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 0.21/0.47    inference(rectify,[],[f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP0(X1,X3,X0)) & (sP0(X1,X3,X0) | ~r2_hidden(X3,X2))) | ~sP1(X0,X1,X2)))),
% 0.21/0.47    inference(nnf_transformation,[],[f13])).
% 0.21/0.47  % (23396)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.47  fof(f153,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~sP0(X0,X1,sK2)) ) | spl7_5),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f134,f46])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | r2_hidden(X1,X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) & ((~r2_hidden(X1,X0) & r2_hidden(X1,X2)) | ~sP0(X0,X1,X2)))),
% 0.21/0.47    inference(rectify,[],[f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ! [X1,X3,X0] : ((sP0(X1,X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP0(X1,X3,X0)))),
% 0.21/0.47    inference(flattening,[],[f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ! [X1,X3,X0] : ((sP0(X1,X3,X0) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP0(X1,X3,X0)))),
% 0.21/0.47    inference(nnf_transformation,[],[f12])).
% 0.21/0.47  fof(f134,plain,(
% 0.21/0.47    ( ! [X0] : (~r2_hidden(X0,sK2)) ) | spl7_5),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f131,f40])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r2_hidden(sK4(X1),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ! [X0,X1] : ((! [X3] : (~r2_hidden(X3,sK4(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK4(X1),X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f11,f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ! [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) => (! [X3] : (~r2_hidden(X3,sK4(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK4(X1),X1)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1] : ~(! [X2] : ~(! [X3] : ~(r2_hidden(X3,X2) & r2_hidden(X3,X1)) & r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).
% 0.21/0.47  fof(f131,plain,(
% 0.21/0.47    ~r2_hidden(sK4(sK2),sK2) | spl7_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f129])).
% 0.21/0.47  fof(f129,plain,(
% 0.21/0.47    spl7_5 <=> r2_hidden(sK4(sK2),sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.47    inference(superposition,[],[f33,f51])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.47    inference(equality_resolution,[],[f39])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 0.21/0.47    inference(cnf_transformation,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.21/0.47    inference(flattening,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.21/0.47    inference(nnf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.21/0.47  fof(f556,plain,(
% 0.21/0.47    ( ! [X0] : (sK2 = k4_xboole_0(sK2,X0)) ) | spl7_5),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f475,f50])).
% 0.21/0.47  fof(f475,plain,(
% 0.21/0.47    ( ! [X0] : (sP1(sK2,X0,sK2)) ) | spl7_5),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f134,f153,f44])).
% 0.21/0.47  fof(f133,plain,(
% 0.21/0.47    ~spl7_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f126,f129])).
% 0.21/0.47  fof(f126,plain,(
% 0.21/0.47    ~r2_hidden(sK4(sK2),sK2)),
% 0.21/0.47    inference(resolution,[],[f124,f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ( ! [X1] : (~r1_xboole_0(X1,sK2) | ~r2_hidden(X1,sK2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X1] : (~r1_xboole_0(X1,sK2) | ~r2_hidden(X1,sK2)) & k1_xboole_0 != sK2),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f9,f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ? [X0] : (! [X1] : (~r1_xboole_0(X1,X0) | ~r2_hidden(X1,X0)) & k1_xboole_0 != X0) => (! [X1] : (~r1_xboole_0(X1,sK2) | ~r2_hidden(X1,sK2)) & k1_xboole_0 != sK2)),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ? [X0] : (! [X1] : (~r1_xboole_0(X1,X0) | ~r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,negated_conjecture,(
% 0.21/0.47    ~! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.47    inference(negated_conjecture,[],[f6])).
% 0.21/0.47  fof(f6,conjecture,(
% 0.21/0.47    ! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).
% 0.21/0.47  fof(f124,plain,(
% 0.21/0.47    ( ! [X0] : (r1_xboole_0(sK4(X0),X0)) )),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f123])).
% 0.21/0.47  fof(f123,plain,(
% 0.21/0.47    ( ! [X0] : (r1_xboole_0(sK4(X0),X0) | r1_xboole_0(sK4(X0),X0)) )),
% 0.21/0.47    inference(resolution,[],[f109,f35])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f10,f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.47    inference(rectify,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.47  fof(f109,plain,(
% 0.21/0.47    ( ! [X2,X3] : (~r2_hidden(sK3(sK4(X2),X3),X2) | r1_xboole_0(sK4(X2),X3)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f106,f54])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r2_hidden(X0,X1) | sP6(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f54_D])).
% 0.21/0.47  fof(f54_D,plain,(
% 0.21/0.47    ( ! [X1] : (( ! [X0] : ~r2_hidden(X0,X1) ) <=> ~sP6(X1)) )),
% 0.21/0.47    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).
% 0.21/0.47  fof(f106,plain,(
% 0.21/0.47    ( ! [X2,X3] : (~r2_hidden(sK3(sK4(X2),X3),X2) | ~sP6(X2) | r1_xboole_0(sK4(X2),X3)) )),
% 0.21/0.47    inference(resolution,[],[f55,f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    ( ! [X3,X1] : (~r2_hidden(X3,sK4(X1)) | ~r2_hidden(X3,X1) | ~sP6(X1)) )),
% 0.21/0.47    inference(general_splitting,[],[f41,f54_D])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    ( ! [X0,X3,X1] : (~r2_hidden(X3,sK4(X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f22])).
% 0.21/0.47  % (23396)Refutation not found, incomplete strategy% (23396)------------------------------
% 0.21/0.47  % (23396)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (23396)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (23396)Memory used [KB]: 6140
% 0.21/0.47  % (23396)Time elapsed: 0.061 s
% 0.21/0.47  % (23396)------------------------------
% 0.21/0.47  % (23396)------------------------------
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    ~spl7_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f31,f57])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    k1_xboole_0 != sK2),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (23412)------------------------------
% 0.21/0.47  % (23412)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (23412)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (23412)Memory used [KB]: 10874
% 0.21/0.47  % (23412)Time elapsed: 0.065 s
% 0.21/0.47  % (23412)------------------------------
% 0.21/0.47  % (23412)------------------------------
% 0.21/0.47  % (23395)Success in time 0.116 s
%------------------------------------------------------------------------------
