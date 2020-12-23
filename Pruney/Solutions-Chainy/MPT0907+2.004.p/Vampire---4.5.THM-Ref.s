%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:21 EST 2020

% Result     : Theorem 0.11s
% Output     : Refutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :   49 (  69 expanded)
%              Number of leaves         :   13 (  28 expanded)
%              Depth                    :    7
%              Number of atoms          :  163 ( 216 expanded)
%              Number of equality atoms :   49 (  75 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f344,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f52,f65,f335,f342,f343])).

fof(f343,plain,
    ( ~ spl8_2
    | ~ spl8_43 ),
    inference(avatar_split_clause,[],[f339,f332,f44])).

fof(f44,plain,
    ( spl8_2
  <=> sK2 = k2_mcart_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f332,plain,
    ( spl8_43
  <=> sK2 = k4_tarski(sK6(sK2,sK4,sK3),sK7(sK2,sK4,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_43])])).

fof(f339,plain,
    ( sK2 != k2_mcart_1(sK2)
    | ~ spl8_43 ),
    inference(superposition,[],[f35,f334])).

fof(f334,plain,
    ( sK2 = k4_tarski(sK6(sK2,sK4,sK3),sK7(sK2,sK4,sK3))
    | ~ spl8_43 ),
    inference(avatar_component_clause,[],[f332])).

fof(f35,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( k2_mcart_1(X0) != X0
      | k4_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0] :
      ( ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f342,plain,
    ( ~ spl8_1
    | ~ spl8_43 ),
    inference(avatar_split_clause,[],[f338,f332,f40])).

fof(f40,plain,
    ( spl8_1
  <=> sK2 = k1_mcart_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f338,plain,
    ( sK2 != k1_mcart_1(sK2)
    | ~ spl8_43 ),
    inference(superposition,[],[f36,f334])).

fof(f36,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != k1_mcart_1(k4_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( k1_mcart_1(X0) != X0
      | k4_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f335,plain,
    ( spl8_43
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f297,f62,f332])).

fof(f62,plain,
    ( spl8_4
  <=> sP0(sK2,sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f297,plain,
    ( sK2 = k4_tarski(sK6(sK2,sK4,sK3),sK7(sK2,sK4,sK3))
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f64,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)) = X0
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3,X4] :
            ( k4_tarski(X3,X4) != X0
            | ~ r2_hidden(X4,X1)
            | ~ r2_hidden(X3,X2) ) )
      & ( ( k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)) = X0
          & r2_hidden(sK7(X0,X1,X2),X1)
          & r2_hidden(sK6(X0,X1,X2),X2) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f17,f18])).

fof(f18,plain,(
    ! [X2,X1,X0] :
      ( ? [X5,X6] :
          ( k4_tarski(X5,X6) = X0
          & r2_hidden(X6,X1)
          & r2_hidden(X5,X2) )
     => ( k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)) = X0
        & r2_hidden(sK7(X0,X1,X2),X1)
        & r2_hidden(sK6(X0,X1,X2),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3,X4] :
            ( k4_tarski(X3,X4) != X0
            | ~ r2_hidden(X4,X1)
            | ~ r2_hidden(X3,X2) ) )
      & ( ? [X5,X6] :
            ( k4_tarski(X5,X6) = X0
            & r2_hidden(X6,X1)
            & r2_hidden(X5,X2) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ! [X3,X1,X0] :
      ( ( sP0(X3,X1,X0)
        | ! [X4,X5] :
            ( k4_tarski(X4,X5) != X3
            | ~ r2_hidden(X5,X1)
            | ~ r2_hidden(X4,X0) ) )
      & ( ? [X4,X5] :
            ( k4_tarski(X4,X5) = X3
            & r2_hidden(X5,X1)
            & r2_hidden(X4,X0) )
        | ~ sP0(X3,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X3,X1,X0] :
      ( sP0(X3,X1,X0)
    <=> ? [X4,X5] :
          ( k4_tarski(X4,X5) = X3
          & r2_hidden(X5,X1)
          & r2_hidden(X4,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f64,plain,
    ( sP0(sK2,sK4,sK3)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f62])).

fof(f65,plain,
    ( spl8_4
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f59,f49,f62])).

fof(f49,plain,
    ( spl8_3
  <=> r2_hidden(sK2,k2_zfmisc_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f59,plain,
    ( sP0(sK2,sK4,sK3)
    | ~ spl8_3 ),
    inference(unit_resulting_resolution,[],[f51,f38,f25])).

fof(f25,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | sP0(X4,X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ~ sP0(sK5(X0,X1,X2),X1,X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( sP0(sK5(X0,X1,X2),X1,X0)
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X4,X1,X0) )
            & ( sP0(X4,X1,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f13,f14])).

fof(f14,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP0(X3,X1,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP0(X3,X1,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP0(sK5(X0,X1,X2),X1,X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( sP0(sK5(X0,X1,X2),X1,X0)
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X3,X1,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X3,X1,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X4,X1,X0) )
            & ( sP0(X4,X1,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X3,X1,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X3,X1,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP0(X3,X1,X0) )
            & ( sP0(X3,X1,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP0(X3,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f38,plain,(
    ! [X0,X1] : sP1(X0,X1,k2_zfmisc_1(X0,X1)) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ~ sP1(X0,X1,X2) )
      & ( sP1(X0,X1,X2)
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> sP1(X0,X1,X2) ) ),
    inference(definition_folding,[],[f1,f8,f7])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f51,plain,
    ( r2_hidden(sK2,k2_zfmisc_1(sK3,sK4))
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f49])).

fof(f52,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f21,f49])).

fof(f21,plain,(
    r2_hidden(sK2,k2_zfmisc_1(sK3,sK4)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( ( sK2 = k2_mcart_1(sK2)
      | sK2 = k1_mcart_1(sK2) )
    & r2_hidden(sK2,k2_zfmisc_1(sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f5,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2] :
        ( ( k2_mcart_1(X0) = X0
          | k1_mcart_1(X0) = X0 )
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) )
   => ( ( sK2 = k2_mcart_1(sK2)
        | sK2 = k1_mcart_1(sK2) )
      & r2_hidden(sK2,k2_zfmisc_1(sK3,sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( ( k2_mcart_1(X0) = X0
        | k1_mcart_1(X0) = X0 )
      & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
       => ( k2_mcart_1(X0) != X0
          & k1_mcart_1(X0) != X0 ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_mcart_1)).

fof(f47,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f22,f44,f40])).

fof(f22,plain,
    ( sK2 = k2_mcart_1(sK2)
    | sK2 = k1_mcart_1(sK2) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : run_vampire %s %d
% 0.11/0.32  % Computer   : n011.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 19:53:57 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.39  % (27279)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.11/0.40  % (27279)Refutation found. Thanks to Tanya!
% 0.11/0.40  % SZS status Theorem for theBenchmark
% 0.11/0.40  % SZS output start Proof for theBenchmark
% 0.11/0.40  fof(f344,plain,(
% 0.11/0.40    $false),
% 0.11/0.40    inference(avatar_sat_refutation,[],[f47,f52,f65,f335,f342,f343])).
% 0.11/0.40  fof(f343,plain,(
% 0.11/0.40    ~spl8_2 | ~spl8_43),
% 0.11/0.40    inference(avatar_split_clause,[],[f339,f332,f44])).
% 0.11/0.40  fof(f44,plain,(
% 0.11/0.40    spl8_2 <=> sK2 = k2_mcart_1(sK2)),
% 0.11/0.40    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.11/0.40  fof(f332,plain,(
% 0.11/0.40    spl8_43 <=> sK2 = k4_tarski(sK6(sK2,sK4,sK3),sK7(sK2,sK4,sK3))),
% 0.11/0.40    introduced(avatar_definition,[new_symbols(naming,[spl8_43])])).
% 0.11/0.40  fof(f339,plain,(
% 0.11/0.40    sK2 != k2_mcart_1(sK2) | ~spl8_43),
% 0.11/0.40    inference(superposition,[],[f35,f334])).
% 0.11/0.40  fof(f334,plain,(
% 0.11/0.40    sK2 = k4_tarski(sK6(sK2,sK4,sK3),sK7(sK2,sK4,sK3)) | ~spl8_43),
% 0.11/0.40    inference(avatar_component_clause,[],[f332])).
% 0.11/0.40  fof(f35,plain,(
% 0.11/0.40    ( ! [X2,X1] : (k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2))) )),
% 0.11/0.40    inference(equality_resolution,[],[f24])).
% 0.11/0.40  fof(f24,plain,(
% 0.11/0.40    ( ! [X2,X0,X1] : (k2_mcart_1(X0) != X0 | k4_tarski(X1,X2) != X0) )),
% 0.11/0.40    inference(cnf_transformation,[],[f6])).
% 0.11/0.40  fof(f6,plain,(
% 0.11/0.40    ! [X0] : ((k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0) | ! [X1,X2] : k4_tarski(X1,X2) != X0)),
% 0.11/0.40    inference(ennf_transformation,[],[f2])).
% 0.11/0.40  fof(f2,axiom,(
% 0.11/0.40    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.11/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).
% 0.11/0.40  fof(f342,plain,(
% 0.11/0.40    ~spl8_1 | ~spl8_43),
% 0.11/0.40    inference(avatar_split_clause,[],[f338,f332,f40])).
% 0.11/0.40  fof(f40,plain,(
% 0.11/0.40    spl8_1 <=> sK2 = k1_mcart_1(sK2)),
% 0.11/0.40    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.11/0.40  fof(f338,plain,(
% 0.11/0.40    sK2 != k1_mcart_1(sK2) | ~spl8_43),
% 0.11/0.40    inference(superposition,[],[f36,f334])).
% 0.11/0.40  fof(f36,plain,(
% 0.11/0.40    ( ! [X2,X1] : (k4_tarski(X1,X2) != k1_mcart_1(k4_tarski(X1,X2))) )),
% 0.11/0.40    inference(equality_resolution,[],[f23])).
% 0.11/0.40  fof(f23,plain,(
% 0.11/0.40    ( ! [X2,X0,X1] : (k1_mcart_1(X0) != X0 | k4_tarski(X1,X2) != X0) )),
% 0.11/0.40    inference(cnf_transformation,[],[f6])).
% 0.11/0.40  fof(f335,plain,(
% 0.11/0.40    spl8_43 | ~spl8_4),
% 0.11/0.40    inference(avatar_split_clause,[],[f297,f62,f332])).
% 0.11/0.40  fof(f62,plain,(
% 0.11/0.40    spl8_4 <=> sP0(sK2,sK4,sK3)),
% 0.11/0.40    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.11/0.40  fof(f297,plain,(
% 0.11/0.40    sK2 = k4_tarski(sK6(sK2,sK4,sK3),sK7(sK2,sK4,sK3)) | ~spl8_4),
% 0.11/0.40    inference(unit_resulting_resolution,[],[f64,f31])).
% 0.11/0.40  fof(f31,plain,(
% 0.11/0.40    ( ! [X2,X0,X1] : (k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)) = X0 | ~sP0(X0,X1,X2)) )),
% 0.11/0.40    inference(cnf_transformation,[],[f19])).
% 0.11/0.40  fof(f19,plain,(
% 0.11/0.40    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3,X4] : (k4_tarski(X3,X4) != X0 | ~r2_hidden(X4,X1) | ~r2_hidden(X3,X2))) & ((k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)) = X0 & r2_hidden(sK7(X0,X1,X2),X1) & r2_hidden(sK6(X0,X1,X2),X2)) | ~sP0(X0,X1,X2)))),
% 0.11/0.40    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f17,f18])).
% 0.11/0.40  fof(f18,plain,(
% 0.11/0.40    ! [X2,X1,X0] : (? [X5,X6] : (k4_tarski(X5,X6) = X0 & r2_hidden(X6,X1) & r2_hidden(X5,X2)) => (k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)) = X0 & r2_hidden(sK7(X0,X1,X2),X1) & r2_hidden(sK6(X0,X1,X2),X2)))),
% 0.11/0.40    introduced(choice_axiom,[])).
% 0.11/0.40  fof(f17,plain,(
% 0.11/0.40    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3,X4] : (k4_tarski(X3,X4) != X0 | ~r2_hidden(X4,X1) | ~r2_hidden(X3,X2))) & (? [X5,X6] : (k4_tarski(X5,X6) = X0 & r2_hidden(X6,X1) & r2_hidden(X5,X2)) | ~sP0(X0,X1,X2)))),
% 0.11/0.40    inference(rectify,[],[f16])).
% 0.11/0.40  fof(f16,plain,(
% 0.11/0.40    ! [X3,X1,X0] : ((sP0(X3,X1,X0) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~sP0(X3,X1,X0)))),
% 0.11/0.40    inference(nnf_transformation,[],[f7])).
% 0.11/0.40  fof(f7,plain,(
% 0.11/0.40    ! [X3,X1,X0] : (sP0(X3,X1,X0) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)))),
% 0.11/0.40    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.11/0.40  fof(f64,plain,(
% 0.11/0.40    sP0(sK2,sK4,sK3) | ~spl8_4),
% 0.11/0.40    inference(avatar_component_clause,[],[f62])).
% 0.11/0.40  fof(f65,plain,(
% 0.11/0.40    spl8_4 | ~spl8_3),
% 0.11/0.40    inference(avatar_split_clause,[],[f59,f49,f62])).
% 0.11/0.40  fof(f49,plain,(
% 0.11/0.40    spl8_3 <=> r2_hidden(sK2,k2_zfmisc_1(sK3,sK4))),
% 0.11/0.40    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.11/0.40  fof(f59,plain,(
% 0.11/0.40    sP0(sK2,sK4,sK3) | ~spl8_3),
% 0.11/0.40    inference(unit_resulting_resolution,[],[f51,f38,f25])).
% 0.11/0.40  fof(f25,plain,(
% 0.11/0.40    ( ! [X4,X2,X0,X1] : (~sP1(X0,X1,X2) | ~r2_hidden(X4,X2) | sP0(X4,X1,X0)) )),
% 0.11/0.40    inference(cnf_transformation,[],[f15])).
% 0.11/0.40  fof(f15,plain,(
% 0.11/0.40    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ((~sP0(sK5(X0,X1,X2),X1,X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sP0(sK5(X0,X1,X2),X1,X0) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X4,X1,X0)) & (sP0(X4,X1,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 0.11/0.40    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f13,f14])).
% 0.11/0.40  fof(f14,plain,(
% 0.11/0.40    ! [X2,X1,X0] : (? [X3] : ((~sP0(X3,X1,X0) | ~r2_hidden(X3,X2)) & (sP0(X3,X1,X0) | r2_hidden(X3,X2))) => ((~sP0(sK5(X0,X1,X2),X1,X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sP0(sK5(X0,X1,X2),X1,X0) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 0.11/0.40    introduced(choice_axiom,[])).
% 0.11/0.40  fof(f13,plain,(
% 0.11/0.40    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X3,X1,X0) | ~r2_hidden(X3,X2)) & (sP0(X3,X1,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X4,X1,X0)) & (sP0(X4,X1,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 0.11/0.40    inference(rectify,[],[f12])).
% 0.11/0.40  fof(f12,plain,(
% 0.11/0.40    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X3,X1,X0) | ~r2_hidden(X3,X2)) & (sP0(X3,X1,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP0(X3,X1,X0)) & (sP0(X3,X1,X0) | ~r2_hidden(X3,X2))) | ~sP1(X0,X1,X2)))),
% 0.11/0.40    inference(nnf_transformation,[],[f8])).
% 0.11/0.40  fof(f8,plain,(
% 0.11/0.40    ! [X0,X1,X2] : (sP1(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP0(X3,X1,X0)))),
% 0.11/0.40    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.11/0.40  fof(f38,plain,(
% 0.11/0.40    ( ! [X0,X1] : (sP1(X0,X1,k2_zfmisc_1(X0,X1))) )),
% 0.11/0.40    inference(equality_resolution,[],[f33])).
% 0.11/0.40  fof(f33,plain,(
% 0.11/0.40    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.11/0.40    inference(cnf_transformation,[],[f20])).
% 0.11/0.40  fof(f20,plain,(
% 0.11/0.40    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ~sP1(X0,X1,X2)) & (sP1(X0,X1,X2) | k2_zfmisc_1(X0,X1) != X2))),
% 0.11/0.40    inference(nnf_transformation,[],[f9])).
% 0.11/0.40  fof(f9,plain,(
% 0.11/0.40    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> sP1(X0,X1,X2))),
% 0.11/0.40    inference(definition_folding,[],[f1,f8,f7])).
% 0.11/0.40  fof(f1,axiom,(
% 0.11/0.40    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 0.11/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 0.11/0.40  fof(f51,plain,(
% 0.11/0.40    r2_hidden(sK2,k2_zfmisc_1(sK3,sK4)) | ~spl8_3),
% 0.11/0.40    inference(avatar_component_clause,[],[f49])).
% 0.11/0.40  fof(f52,plain,(
% 0.11/0.40    spl8_3),
% 0.11/0.40    inference(avatar_split_clause,[],[f21,f49])).
% 0.11/0.40  fof(f21,plain,(
% 0.11/0.40    r2_hidden(sK2,k2_zfmisc_1(sK3,sK4))),
% 0.11/0.40    inference(cnf_transformation,[],[f11])).
% 0.11/0.40  fof(f11,plain,(
% 0.11/0.40    (sK2 = k2_mcart_1(sK2) | sK2 = k1_mcart_1(sK2)) & r2_hidden(sK2,k2_zfmisc_1(sK3,sK4))),
% 0.11/0.40    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f5,f10])).
% 0.11/0.40  fof(f10,plain,(
% 0.11/0.40    ? [X0,X1,X2] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & r2_hidden(X0,k2_zfmisc_1(X1,X2))) => ((sK2 = k2_mcart_1(sK2) | sK2 = k1_mcart_1(sK2)) & r2_hidden(sK2,k2_zfmisc_1(sK3,sK4)))),
% 0.11/0.40    introduced(choice_axiom,[])).
% 0.11/0.40  fof(f5,plain,(
% 0.11/0.40    ? [X0,X1,X2] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.11/0.40    inference(ennf_transformation,[],[f4])).
% 0.11/0.40  fof(f4,negated_conjecture,(
% 0.11/0.40    ~! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.11/0.40    inference(negated_conjecture,[],[f3])).
% 0.11/0.40  fof(f3,conjecture,(
% 0.11/0.40    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.11/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_mcart_1)).
% 0.11/0.40  fof(f47,plain,(
% 0.11/0.40    spl8_1 | spl8_2),
% 0.11/0.40    inference(avatar_split_clause,[],[f22,f44,f40])).
% 0.11/0.40  fof(f22,plain,(
% 0.11/0.40    sK2 = k2_mcart_1(sK2) | sK2 = k1_mcart_1(sK2)),
% 0.11/0.40    inference(cnf_transformation,[],[f11])).
% 0.11/0.40  % SZS output end Proof for theBenchmark
% 0.11/0.40  % (27279)------------------------------
% 0.11/0.40  % (27279)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.11/0.40  % (27279)Termination reason: Refutation
% 0.11/0.40  
% 0.11/0.40  % (27279)Memory used [KB]: 11001
% 0.11/0.40  % (27279)Time elapsed: 0.007 s
% 0.11/0.40  % (27279)------------------------------
% 0.11/0.40  % (27279)------------------------------
% 0.11/0.40  % (27261)Success in time 0.061 s
%------------------------------------------------------------------------------
