%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:50 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 216 expanded)
%              Number of leaves         :   14 (  75 expanded)
%              Depth                    :    9
%              Number of atoms          :  217 ( 766 expanded)
%              Number of equality atoms :   10 (  50 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f89,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f47,f64,f66,f68,f70,f72,f78,f84,f86,f87,f88])).

fof(f88,plain,
    ( spl8_1
    | spl8_4 ),
    inference(avatar_split_clause,[],[f33,f57,f35])).

fof(f35,plain,
    ( spl8_1
  <=> r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f57,plain,
    ( spl8_4
  <=> r2_hidden(sK0,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f33,plain,
    ( r2_hidden(sK0,sK4)
    | r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
    inference(definition_unfolding,[],[f15,f27,f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f23,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f23,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f27,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f22,f20])).

fof(f20,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f22,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).

fof(f15,plain,
    ( r2_hidden(sK0,sK4)
    | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ( ~ r2_hidden(sK3,sK7)
      | ~ r2_hidden(sK2,sK6)
      | ~ r2_hidden(sK1,sK5)
      | ~ r2_hidden(sK0,sK4)
      | ~ r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) )
    & ( ( r2_hidden(sK3,sK7)
        & r2_hidden(sK2,sK6)
        & r2_hidden(sK1,sK5)
        & r2_hidden(sK0,sK4) )
      | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f10,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( ( ~ r2_hidden(X3,X7)
          | ~ r2_hidden(X2,X6)
          | ~ r2_hidden(X1,X5)
          | ~ r2_hidden(X0,X4)
          | ~ r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) )
        & ( ( r2_hidden(X3,X7)
            & r2_hidden(X2,X6)
            & r2_hidden(X1,X5)
            & r2_hidden(X0,X4) )
          | r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) ) )
   => ( ( ~ r2_hidden(sK3,sK7)
        | ~ r2_hidden(sK2,sK6)
        | ~ r2_hidden(sK1,sK5)
        | ~ r2_hidden(sK0,sK4)
        | ~ r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) )
      & ( ( r2_hidden(sK3,sK7)
          & r2_hidden(sK2,sK6)
          & r2_hidden(sK1,sK5)
          & r2_hidden(sK0,sK4) )
        | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( ~ r2_hidden(X3,X7)
        | ~ r2_hidden(X2,X6)
        | ~ r2_hidden(X1,X5)
        | ~ r2_hidden(X0,X4)
        | ~ r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) )
      & ( ( r2_hidden(X3,X7)
          & r2_hidden(X2,X6)
          & r2_hidden(X1,X5)
          & r2_hidden(X0,X4) )
        | r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) ) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( ~ r2_hidden(X3,X7)
        | ~ r2_hidden(X2,X6)
        | ~ r2_hidden(X1,X5)
        | ~ r2_hidden(X0,X4)
        | ~ r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) )
      & ( ( r2_hidden(X3,X7)
          & r2_hidden(X2,X6)
          & r2_hidden(X1,X5)
          & r2_hidden(X0,X4) )
        | r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))
    <~> ( r2_hidden(X3,X7)
        & r2_hidden(X2,X6)
        & r2_hidden(X1,X5)
        & r2_hidden(X0,X4) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))
      <=> ( r2_hidden(X3,X7)
          & r2_hidden(X2,X6)
          & r2_hidden(X1,X5)
          & r2_hidden(X0,X4) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))
    <=> ( r2_hidden(X3,X7)
        & r2_hidden(X2,X6)
        & r2_hidden(X1,X5)
        & r2_hidden(X0,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_mcart_1)).

fof(f87,plain,
    ( spl8_1
    | spl8_5 ),
    inference(avatar_split_clause,[],[f32,f61,f35])).

fof(f61,plain,
    ( spl8_5
  <=> r2_hidden(sK1,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f32,plain,
    ( r2_hidden(sK1,sK5)
    | r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
    inference(definition_unfolding,[],[f16,f27,f28])).

fof(f16,plain,
    ( r2_hidden(sK1,sK5)
    | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f12])).

fof(f86,plain,
    ( ~ spl8_4
    | ~ spl8_5
    | spl8_7 ),
    inference(avatar_split_clause,[],[f85,f81,f61,f57])).

fof(f81,plain,
    ( spl8_7
  <=> r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f85,plain,
    ( ~ r2_hidden(sK1,sK5)
    | ~ r2_hidden(sK0,sK4)
    | spl8_7 ),
    inference(resolution,[],[f83,f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(f83,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK4,sK5))
    | spl8_7 ),
    inference(avatar_component_clause,[],[f81])).

fof(f84,plain,
    ( ~ spl8_7
    | ~ spl8_3
    | spl8_6 ),
    inference(avatar_split_clause,[],[f79,f75,f44,f81])).

fof(f44,plain,
    ( spl8_3
  <=> r2_hidden(sK2,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f75,plain,
    ( spl8_6
  <=> r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f79,plain,
    ( ~ r2_hidden(sK2,sK6)
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK4,sK5))
    | spl8_6 ),
    inference(resolution,[],[f77,f26])).

fof(f77,plain,
    ( ~ r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))
    | spl8_6 ),
    inference(avatar_component_clause,[],[f75])).

fof(f78,plain,
    ( ~ spl8_6
    | ~ spl8_2
    | spl8_1 ),
    inference(avatar_split_clause,[],[f73,f35,f39,f75])).

fof(f39,plain,
    ( spl8_2
  <=> r2_hidden(sK3,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f73,plain,
    ( ~ r2_hidden(sK3,sK7)
    | ~ r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))
    | spl8_1 ),
    inference(resolution,[],[f36,f26])).

fof(f36,plain,
    ( ~ r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f72,plain,
    ( ~ spl8_1
    | spl8_2 ),
    inference(avatar_contradiction_clause,[],[f71])).

fof(f71,plain,
    ( $false
    | ~ spl8_1
    | spl8_2 ),
    inference(resolution,[],[f48,f40])).

fof(f40,plain,
    ( ~ r2_hidden(sK3,sK7)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f48,plain,
    ( r2_hidden(sK3,sK7)
    | ~ spl8_1 ),
    inference(resolution,[],[f37,f25])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f37,plain,
    ( r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f70,plain,
    ( ~ spl8_1
    | spl8_5 ),
    inference(avatar_contradiction_clause,[],[f69])).

fof(f69,plain,
    ( $false
    | ~ spl8_1
    | spl8_5 ),
    inference(resolution,[],[f63,f52])).

fof(f52,plain,
    ( r2_hidden(sK1,sK5)
    | ~ spl8_1 ),
    inference(resolution,[],[f51,f25])).

fof(f51,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK4,sK5))
    | ~ spl8_1 ),
    inference(resolution,[],[f49,f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f49,plain,
    ( r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))
    | ~ spl8_1 ),
    inference(resolution,[],[f37,f24])).

fof(f63,plain,
    ( ~ r2_hidden(sK1,sK5)
    | spl8_5 ),
    inference(avatar_component_clause,[],[f61])).

fof(f68,plain,
    ( ~ spl8_1
    | spl8_4 ),
    inference(avatar_contradiction_clause,[],[f67])).

fof(f67,plain,
    ( $false
    | ~ spl8_1
    | spl8_4 ),
    inference(resolution,[],[f59,f53])).

fof(f53,plain,
    ( r2_hidden(sK0,sK4)
    | ~ spl8_1 ),
    inference(resolution,[],[f51,f24])).

fof(f59,plain,
    ( ~ r2_hidden(sK0,sK4)
    | spl8_4 ),
    inference(avatar_component_clause,[],[f57])).

fof(f66,plain,
    ( ~ spl8_1
    | spl8_3 ),
    inference(avatar_contradiction_clause,[],[f65])).

fof(f65,plain,
    ( $false
    | ~ spl8_1
    | spl8_3 ),
    inference(resolution,[],[f45,f50])).

fof(f50,plain,
    ( r2_hidden(sK2,sK6)
    | ~ spl8_1 ),
    inference(resolution,[],[f49,f25])).

fof(f45,plain,
    ( ~ r2_hidden(sK2,sK6)
    | spl8_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f64,plain,
    ( ~ spl8_1
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_3
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f29,f39,f44,f61,f57,f35])).

fof(f29,plain,
    ( ~ r2_hidden(sK3,sK7)
    | ~ r2_hidden(sK2,sK6)
    | ~ r2_hidden(sK1,sK5)
    | ~ r2_hidden(sK0,sK4)
    | ~ r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
    inference(definition_unfolding,[],[f19,f27,f28])).

fof(f19,plain,
    ( ~ r2_hidden(sK3,sK7)
    | ~ r2_hidden(sK2,sK6)
    | ~ r2_hidden(sK1,sK5)
    | ~ r2_hidden(sK0,sK4)
    | ~ r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f12])).

fof(f47,plain,
    ( spl8_1
    | spl8_3 ),
    inference(avatar_split_clause,[],[f31,f44,f35])).

fof(f31,plain,
    ( r2_hidden(sK2,sK6)
    | r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
    inference(definition_unfolding,[],[f17,f27,f28])).

fof(f17,plain,
    ( r2_hidden(sK2,sK6)
    | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f12])).

fof(f42,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f30,f39,f35])).

fof(f30,plain,
    ( r2_hidden(sK3,sK7)
    | r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
    inference(definition_unfolding,[],[f18,f27,f28])).

fof(f18,plain,
    ( r2_hidden(sK3,sK7)
    | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:25:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (21619)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.50  % (21614)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.50  % (21615)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.50  % (21606)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.50  % (21611)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.50  % (21612)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (21609)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.50  % (21607)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.50  % (21608)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.51  % (21608)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f89,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f42,f47,f64,f66,f68,f70,f72,f78,f84,f86,f87,f88])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    spl8_1 | spl8_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f33,f57,f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    spl8_1 <=> r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    spl8_4 <=> r2_hidden(sK0,sK4)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    r2_hidden(sK0,sK4) | r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))),
% 0.21/0.51    inference(definition_unfolding,[],[f15,f27,f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f23,f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f22,f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    r2_hidden(sK0,sK4) | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    (~r2_hidden(sK3,sK7) | ~r2_hidden(sK2,sK6) | ~r2_hidden(sK1,sK5) | ~r2_hidden(sK0,sK4) | ~r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7))) & ((r2_hidden(sK3,sK7) & r2_hidden(sK2,sK6) & r2_hidden(sK1,sK5) & r2_hidden(sK0,sK4)) | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f10,f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((~r2_hidden(X3,X7) | ~r2_hidden(X2,X6) | ~r2_hidden(X1,X5) | ~r2_hidden(X0,X4) | ~r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))) & ((r2_hidden(X3,X7) & r2_hidden(X2,X6) & r2_hidden(X1,X5) & r2_hidden(X0,X4)) | r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)))) => ((~r2_hidden(sK3,sK7) | ~r2_hidden(sK2,sK6) | ~r2_hidden(sK1,sK5) | ~r2_hidden(sK0,sK4) | ~r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7))) & ((r2_hidden(sK3,sK7) & r2_hidden(sK2,sK6) & r2_hidden(sK1,sK5) & r2_hidden(sK0,sK4)) | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((~r2_hidden(X3,X7) | ~r2_hidden(X2,X6) | ~r2_hidden(X1,X5) | ~r2_hidden(X0,X4) | ~r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))) & ((r2_hidden(X3,X7) & r2_hidden(X2,X6) & r2_hidden(X1,X5) & r2_hidden(X0,X4)) | r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))))),
% 0.21/0.51    inference(flattening,[],[f9])).
% 0.21/0.51  fof(f9,plain,(
% 0.21/0.51    ? [X0,X1,X2,X3,X4,X5,X6,X7] : (((~r2_hidden(X3,X7) | ~r2_hidden(X2,X6) | ~r2_hidden(X1,X5) | ~r2_hidden(X0,X4)) | ~r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))) & ((r2_hidden(X3,X7) & r2_hidden(X2,X6) & r2_hidden(X1,X5) & r2_hidden(X0,X4)) | r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))))),
% 0.21/0.51    inference(nnf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,plain,(
% 0.21/0.51    ? [X0,X1,X2,X3,X4,X5,X6,X7] : (r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) <~> (r2_hidden(X3,X7) & r2_hidden(X2,X6) & r2_hidden(X1,X5) & r2_hidden(X0,X4)))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : (r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) <=> (r2_hidden(X3,X7) & r2_hidden(X2,X6) & r2_hidden(X1,X5) & r2_hidden(X0,X4)))),
% 0.21/0.51    inference(negated_conjecture,[],[f6])).
% 0.21/0.51  fof(f6,conjecture,(
% 0.21/0.51    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) <=> (r2_hidden(X3,X7) & r2_hidden(X2,X6) & r2_hidden(X1,X5) & r2_hidden(X0,X4)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_mcart_1)).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    spl8_1 | spl8_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f32,f61,f35])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    spl8_5 <=> r2_hidden(sK1,sK5)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    r2_hidden(sK1,sK5) | r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))),
% 0.21/0.51    inference(definition_unfolding,[],[f16,f27,f28])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    r2_hidden(sK1,sK5) | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    ~spl8_4 | ~spl8_5 | spl8_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f85,f81,f61,f57])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    spl8_7 <=> r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK4,sK5))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    ~r2_hidden(sK1,sK5) | ~r2_hidden(sK0,sK4) | spl8_7),
% 0.21/0.51    inference(resolution,[],[f83,f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.21/0.51    inference(flattening,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.21/0.51    inference(nnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_zfmisc_1)).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK4,sK5)) | spl8_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f81])).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    ~spl8_7 | ~spl8_3 | spl8_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f79,f75,f44,f81])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    spl8_3 <=> r2_hidden(sK2,sK6)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    spl8_6 <=> r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    ~r2_hidden(sK2,sK6) | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK4,sK5)) | spl8_6),
% 0.21/0.51    inference(resolution,[],[f77,f26])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    ~r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) | spl8_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f75])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    ~spl8_6 | ~spl8_2 | spl8_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f73,f35,f39,f75])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    spl8_2 <=> r2_hidden(sK3,sK7)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    ~r2_hidden(sK3,sK7) | ~r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) | spl8_1),
% 0.21/0.51    inference(resolution,[],[f36,f26])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ~r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) | spl8_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f35])).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    ~spl8_1 | spl8_2),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f71])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    $false | (~spl8_1 | spl8_2)),
% 0.21/0.51    inference(resolution,[],[f48,f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ~r2_hidden(sK3,sK7) | spl8_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f39])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    r2_hidden(sK3,sK7) | ~spl8_1),
% 0.21/0.51    inference(resolution,[],[f37,f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) | ~spl8_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f35])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    ~spl8_1 | spl8_5),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f69])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    $false | (~spl8_1 | spl8_5)),
% 0.21/0.51    inference(resolution,[],[f63,f52])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    r2_hidden(sK1,sK5) | ~spl8_1),
% 0.21/0.51    inference(resolution,[],[f51,f25])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK4,sK5)) | ~spl8_1),
% 0.21/0.51    inference(resolution,[],[f49,f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) | ~spl8_1),
% 0.21/0.51    inference(resolution,[],[f37,f24])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    ~r2_hidden(sK1,sK5) | spl8_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f61])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    ~spl8_1 | spl8_4),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f67])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    $false | (~spl8_1 | spl8_4)),
% 0.21/0.51    inference(resolution,[],[f59,f53])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    r2_hidden(sK0,sK4) | ~spl8_1),
% 0.21/0.51    inference(resolution,[],[f51,f24])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    ~r2_hidden(sK0,sK4) | spl8_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f57])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    ~spl8_1 | spl8_3),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f65])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    $false | (~spl8_1 | spl8_3)),
% 0.21/0.51    inference(resolution,[],[f45,f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    r2_hidden(sK2,sK6) | ~spl8_1),
% 0.21/0.51    inference(resolution,[],[f49,f25])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ~r2_hidden(sK2,sK6) | spl8_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f44])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    ~spl8_1 | ~spl8_4 | ~spl8_5 | ~spl8_3 | ~spl8_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f29,f39,f44,f61,f57,f35])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ~r2_hidden(sK3,sK7) | ~r2_hidden(sK2,sK6) | ~r2_hidden(sK1,sK5) | ~r2_hidden(sK0,sK4) | ~r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))),
% 0.21/0.51    inference(definition_unfolding,[],[f19,f27,f28])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ~r2_hidden(sK3,sK7) | ~r2_hidden(sK2,sK6) | ~r2_hidden(sK1,sK5) | ~r2_hidden(sK0,sK4) | ~r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    spl8_1 | spl8_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f31,f44,f35])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    r2_hidden(sK2,sK6) | r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))),
% 0.21/0.51    inference(definition_unfolding,[],[f17,f27,f28])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    r2_hidden(sK2,sK6) | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    spl8_1 | spl8_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f30,f39,f35])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    r2_hidden(sK3,sK7) | r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))),
% 0.21/0.51    inference(definition_unfolding,[],[f18,f27,f28])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    r2_hidden(sK3,sK7) | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (21608)------------------------------
% 0.21/0.51  % (21608)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (21608)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (21608)Memory used [KB]: 6140
% 0.21/0.51  % (21608)Time elapsed: 0.070 s
% 0.21/0.51  % (21608)------------------------------
% 0.21/0.51  % (21608)------------------------------
% 0.21/0.51  % (21620)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.51  % (21605)Success in time 0.152 s
%------------------------------------------------------------------------------
