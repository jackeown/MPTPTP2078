%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:51 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 202 expanded)
%              Number of leaves         :   15 (  70 expanded)
%              Depth                    :    9
%              Number of atoms          :  244 ( 779 expanded)
%              Number of equality atoms :    8 (  24 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f110,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f64,f65,f66,f67,f75,f81,f83,f93,f95,f97,f103,f109])).

fof(f109,plain,
    ( ~ spl8_1
    | spl8_5 ),
    inference(avatar_contradiction_clause,[],[f108])).

fof(f108,plain,
    ( $false
    | ~ spl8_1
    | spl8_5 ),
    inference(resolution,[],[f84,f62])).

fof(f62,plain,
    ( ~ r2_hidden(sK3,sK7)
    | spl8_5 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl8_5
  <=> r2_hidden(sK3,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f84,plain,
    ( r2_hidden(sK3,sK7)
    | ~ spl8_1 ),
    inference(resolution,[],[f45,f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f45,plain,
    ( r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl8_1
  <=> r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f103,plain,
    ( ~ spl8_1
    | spl8_4 ),
    inference(avatar_contradiction_clause,[],[f102])).

fof(f102,plain,
    ( $false
    | ~ spl8_1
    | spl8_4 ),
    inference(resolution,[],[f98,f58])).

fof(f58,plain,
    ( ~ r2_hidden(sK2,sK6)
    | spl8_4 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl8_4
  <=> r2_hidden(sK2,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f98,plain,
    ( r2_hidden(sK2,sK6)
    | ~ spl8_1 ),
    inference(resolution,[],[f41,f45])).

fof(f41,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(k4_tarski(k4_tarski(X0,X1),X2),k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5))
      | r2_hidden(X1,X4) ) ),
    inference(definition_unfolding,[],[f31,f23,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f23,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f31,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_hidden(X1,X4)
      | ~ r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))
        | ~ r2_hidden(X2,X5)
        | ~ r2_hidden(X1,X4)
        | ~ r2_hidden(X0,X3) )
      & ( ( r2_hidden(X2,X5)
          & r2_hidden(X1,X4)
          & r2_hidden(X0,X3) )
        | ~ r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))
        | ~ r2_hidden(X2,X5)
        | ~ r2_hidden(X1,X4)
        | ~ r2_hidden(X0,X3) )
      & ( ( r2_hidden(X2,X5)
          & r2_hidden(X1,X4)
          & r2_hidden(X0,X3) )
        | ~ r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))
    <=> ( r2_hidden(X2,X5)
        & r2_hidden(X1,X4)
        & r2_hidden(X0,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_mcart_1)).

fof(f97,plain,
    ( ~ spl8_1
    | spl8_3 ),
    inference(avatar_contradiction_clause,[],[f96])).

fof(f96,plain,
    ( $false
    | ~ spl8_1
    | spl8_3 ),
    inference(resolution,[],[f91,f54])).

fof(f54,plain,
    ( ~ r2_hidden(sK1,sK5)
    | spl8_3 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl8_3
  <=> r2_hidden(sK1,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f91,plain,
    ( r2_hidden(sK1,sK5)
    | ~ spl8_1 ),
    inference(resolution,[],[f88,f28])).

fof(f88,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK4,sK5))
    | ~ spl8_1 ),
    inference(resolution,[],[f85,f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f85,plain,
    ( r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))
    | ~ spl8_1 ),
    inference(resolution,[],[f45,f27])).

fof(f95,plain,
    ( ~ spl8_1
    | spl8_2 ),
    inference(avatar_contradiction_clause,[],[f94])).

fof(f94,plain,
    ( $false
    | ~ spl8_1
    | spl8_2 ),
    inference(resolution,[],[f92,f50])).

fof(f50,plain,
    ( ~ r2_hidden(sK0,sK4)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl8_2
  <=> r2_hidden(sK0,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f92,plain,
    ( r2_hidden(sK0,sK4)
    | ~ spl8_1 ),
    inference(resolution,[],[f88,f27])).

fof(f93,plain,
    ( ~ spl8_1
    | spl8_7 ),
    inference(avatar_contradiction_clause,[],[f90])).

fof(f90,plain,
    ( $false
    | ~ spl8_1
    | spl8_7 ),
    inference(resolution,[],[f88,f80])).

fof(f80,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK4,sK5))
    | spl8_7 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl8_7
  <=> r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f83,plain,
    ( ~ spl8_2
    | ~ spl8_3
    | spl8_7 ),
    inference(avatar_split_clause,[],[f82,f78,f52,f48])).

fof(f82,plain,
    ( ~ r2_hidden(sK1,sK5)
    | ~ r2_hidden(sK0,sK4)
    | spl8_7 ),
    inference(resolution,[],[f80,f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f81,plain,
    ( ~ spl8_7
    | ~ spl8_4
    | spl8_6 ),
    inference(avatar_split_clause,[],[f76,f72,f56,f78])).

fof(f72,plain,
    ( spl8_6
  <=> r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f76,plain,
    ( ~ r2_hidden(sK2,sK6)
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK4,sK5))
    | spl8_6 ),
    inference(resolution,[],[f74,f29])).

fof(f74,plain,
    ( ~ r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))
    | spl8_6 ),
    inference(avatar_component_clause,[],[f72])).

fof(f75,plain,
    ( ~ spl8_6
    | ~ spl8_5
    | spl8_1 ),
    inference(avatar_split_clause,[],[f70,f44,f60,f72])).

fof(f70,plain,
    ( ~ r2_hidden(sK3,sK7)
    | ~ r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))
    | spl8_1 ),
    inference(resolution,[],[f29,f46])).

fof(f46,plain,
    ( ~ r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f44])).

fof(f67,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f38,f48,f44])).

fof(f38,plain,
    ( r2_hidden(sK0,sK4)
    | r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
    inference(definition_unfolding,[],[f18,f25,f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_mcart_1)).

fof(f25,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_mcart_1)).

fof(f18,plain,
    ( r2_hidden(sK0,sK4)
    | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f11,f12])).

fof(f12,plain,
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

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

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
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))
    <~> ( r2_hidden(X3,X7)
        & r2_hidden(X2,X6)
        & r2_hidden(X1,X5)
        & r2_hidden(X0,X4) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))
      <=> ( r2_hidden(X3,X7)
          & r2_hidden(X2,X6)
          & r2_hidden(X1,X5)
          & r2_hidden(X0,X4) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))
    <=> ( r2_hidden(X3,X7)
        & r2_hidden(X2,X6)
        & r2_hidden(X1,X5)
        & r2_hidden(X0,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_mcart_1)).

fof(f66,plain,
    ( spl8_1
    | spl8_3 ),
    inference(avatar_split_clause,[],[f37,f52,f44])).

fof(f37,plain,
    ( r2_hidden(sK1,sK5)
    | r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
    inference(definition_unfolding,[],[f19,f25,f26])).

fof(f19,plain,
    ( r2_hidden(sK1,sK5)
    | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f13])).

fof(f65,plain,
    ( spl8_1
    | spl8_4 ),
    inference(avatar_split_clause,[],[f36,f56,f44])).

fof(f36,plain,
    ( r2_hidden(sK2,sK6)
    | r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
    inference(definition_unfolding,[],[f20,f25,f26])).

fof(f20,plain,
    ( r2_hidden(sK2,sK6)
    | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f13])).

fof(f64,plain,
    ( spl8_1
    | spl8_5 ),
    inference(avatar_split_clause,[],[f35,f60,f44])).

fof(f35,plain,
    ( r2_hidden(sK3,sK7)
    | r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
    inference(definition_unfolding,[],[f21,f25,f26])).

fof(f21,plain,
    ( r2_hidden(sK3,sK7)
    | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f13])).

fof(f63,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f34,f60,f56,f52,f48,f44])).

fof(f34,plain,
    ( ~ r2_hidden(sK3,sK7)
    | ~ r2_hidden(sK2,sK6)
    | ~ r2_hidden(sK1,sK5)
    | ~ r2_hidden(sK0,sK4)
    | ~ r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
    inference(definition_unfolding,[],[f22,f25,f26])).

fof(f22,plain,
    ( ~ r2_hidden(sK3,sK7)
    | ~ r2_hidden(sK2,sK6)
    | ~ r2_hidden(sK1,sK5)
    | ~ r2_hidden(sK0,sK4)
    | ~ r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:59:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.42  % (22042)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.44  % (22029)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.45  % (22032)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.45  % (22032)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f110,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(avatar_sat_refutation,[],[f63,f64,f65,f66,f67,f75,f81,f83,f93,f95,f97,f103,f109])).
% 0.21/0.45  fof(f109,plain,(
% 0.21/0.45    ~spl8_1 | spl8_5),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f108])).
% 0.21/0.45  fof(f108,plain,(
% 0.21/0.45    $false | (~spl8_1 | spl8_5)),
% 0.21/0.45    inference(resolution,[],[f84,f62])).
% 0.21/0.45  fof(f62,plain,(
% 0.21/0.45    ~r2_hidden(sK3,sK7) | spl8_5),
% 0.21/0.45    inference(avatar_component_clause,[],[f60])).
% 0.21/0.45  fof(f60,plain,(
% 0.21/0.45    spl8_5 <=> r2_hidden(sK3,sK7)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.21/0.45  fof(f84,plain,(
% 0.21/0.45    r2_hidden(sK3,sK7) | ~spl8_1),
% 0.21/0.45    inference(resolution,[],[f45,f28])).
% 0.21/0.45  fof(f28,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f15])).
% 0.21/0.45  fof(f15,plain,(
% 0.21/0.45    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.21/0.45    inference(flattening,[],[f14])).
% 0.21/0.45  fof(f14,plain,(
% 0.21/0.45    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.21/0.45    inference(nnf_transformation,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.21/0.45  fof(f45,plain,(
% 0.21/0.45    r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) | ~spl8_1),
% 0.21/0.45    inference(avatar_component_clause,[],[f44])).
% 0.21/0.45  fof(f44,plain,(
% 0.21/0.45    spl8_1 <=> r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.45  fof(f103,plain,(
% 0.21/0.45    ~spl8_1 | spl8_4),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f102])).
% 0.21/0.45  fof(f102,plain,(
% 0.21/0.45    $false | (~spl8_1 | spl8_4)),
% 0.21/0.45    inference(resolution,[],[f98,f58])).
% 0.21/0.45  fof(f58,plain,(
% 0.21/0.45    ~r2_hidden(sK2,sK6) | spl8_4),
% 0.21/0.45    inference(avatar_component_clause,[],[f56])).
% 0.21/0.45  fof(f56,plain,(
% 0.21/0.45    spl8_4 <=> r2_hidden(sK2,sK6)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.45  fof(f98,plain,(
% 0.21/0.45    r2_hidden(sK2,sK6) | ~spl8_1),
% 0.21/0.45    inference(resolution,[],[f41,f45])).
% 0.21/0.45  fof(f41,plain,(
% 0.21/0.45    ( ! [X4,X2,X0,X5,X3,X1] : (~r2_hidden(k4_tarski(k4_tarski(X0,X1),X2),k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)) | r2_hidden(X1,X4)) )),
% 0.21/0.45    inference(definition_unfolding,[],[f31,f23,f24])).
% 0.21/0.45  fof(f24,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f3])).
% 0.21/0.45  fof(f3,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.21/0.45  fof(f31,plain,(
% 0.21/0.45    ( ! [X4,X2,X0,X5,X3,X1] : (r2_hidden(X1,X4) | ~r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f17])).
% 0.21/0.45  fof(f17,plain,(
% 0.21/0.45    ! [X0,X1,X2,X3,X4,X5] : ((r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) | ~r2_hidden(X2,X5) | ~r2_hidden(X1,X4) | ~r2_hidden(X0,X3)) & ((r2_hidden(X2,X5) & r2_hidden(X1,X4) & r2_hidden(X0,X3)) | ~r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))))),
% 0.21/0.45    inference(flattening,[],[f16])).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    ! [X0,X1,X2,X3,X4,X5] : ((r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) | (~r2_hidden(X2,X5) | ~r2_hidden(X1,X4) | ~r2_hidden(X0,X3))) & ((r2_hidden(X2,X5) & r2_hidden(X1,X4) & r2_hidden(X0,X3)) | ~r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))))),
% 0.21/0.45    inference(nnf_transformation,[],[f6])).
% 0.21/0.45  fof(f6,axiom,(
% 0.21/0.45    ! [X0,X1,X2,X3,X4,X5] : (r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) <=> (r2_hidden(X2,X5) & r2_hidden(X1,X4) & r2_hidden(X0,X3)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_mcart_1)).
% 0.21/0.45  fof(f97,plain,(
% 0.21/0.45    ~spl8_1 | spl8_3),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f96])).
% 0.21/0.45  fof(f96,plain,(
% 0.21/0.45    $false | (~spl8_1 | spl8_3)),
% 0.21/0.45    inference(resolution,[],[f91,f54])).
% 0.21/0.45  fof(f54,plain,(
% 0.21/0.45    ~r2_hidden(sK1,sK5) | spl8_3),
% 0.21/0.45    inference(avatar_component_clause,[],[f52])).
% 0.21/0.45  fof(f52,plain,(
% 0.21/0.45    spl8_3 <=> r2_hidden(sK1,sK5)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.45  fof(f91,plain,(
% 0.21/0.45    r2_hidden(sK1,sK5) | ~spl8_1),
% 0.21/0.45    inference(resolution,[],[f88,f28])).
% 0.21/0.45  fof(f88,plain,(
% 0.21/0.45    r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK4,sK5)) | ~spl8_1),
% 0.21/0.45    inference(resolution,[],[f85,f27])).
% 0.21/0.45  fof(f27,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f15])).
% 0.21/0.45  fof(f85,plain,(
% 0.21/0.45    r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) | ~spl8_1),
% 0.21/0.45    inference(resolution,[],[f45,f27])).
% 0.21/0.45  fof(f95,plain,(
% 0.21/0.45    ~spl8_1 | spl8_2),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f94])).
% 0.21/0.45  fof(f94,plain,(
% 0.21/0.45    $false | (~spl8_1 | spl8_2)),
% 0.21/0.45    inference(resolution,[],[f92,f50])).
% 0.21/0.45  fof(f50,plain,(
% 0.21/0.45    ~r2_hidden(sK0,sK4) | spl8_2),
% 0.21/0.45    inference(avatar_component_clause,[],[f48])).
% 0.21/0.45  fof(f48,plain,(
% 0.21/0.45    spl8_2 <=> r2_hidden(sK0,sK4)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.45  fof(f92,plain,(
% 0.21/0.45    r2_hidden(sK0,sK4) | ~spl8_1),
% 0.21/0.45    inference(resolution,[],[f88,f27])).
% 0.21/0.45  fof(f93,plain,(
% 0.21/0.45    ~spl8_1 | spl8_7),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f90])).
% 0.21/0.45  fof(f90,plain,(
% 0.21/0.45    $false | (~spl8_1 | spl8_7)),
% 0.21/0.45    inference(resolution,[],[f88,f80])).
% 0.21/0.45  fof(f80,plain,(
% 0.21/0.45    ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK4,sK5)) | spl8_7),
% 0.21/0.45    inference(avatar_component_clause,[],[f78])).
% 0.21/0.45  fof(f78,plain,(
% 0.21/0.45    spl8_7 <=> r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK4,sK5))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.21/0.45  fof(f83,plain,(
% 0.21/0.45    ~spl8_2 | ~spl8_3 | spl8_7),
% 0.21/0.45    inference(avatar_split_clause,[],[f82,f78,f52,f48])).
% 0.21/0.45  fof(f82,plain,(
% 0.21/0.45    ~r2_hidden(sK1,sK5) | ~r2_hidden(sK0,sK4) | spl8_7),
% 0.21/0.45    inference(resolution,[],[f80,f29])).
% 0.21/0.45  fof(f29,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f15])).
% 0.21/0.45  fof(f81,plain,(
% 0.21/0.45    ~spl8_7 | ~spl8_4 | spl8_6),
% 0.21/0.45    inference(avatar_split_clause,[],[f76,f72,f56,f78])).
% 0.21/0.45  fof(f72,plain,(
% 0.21/0.45    spl8_6 <=> r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.21/0.45  fof(f76,plain,(
% 0.21/0.45    ~r2_hidden(sK2,sK6) | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK4,sK5)) | spl8_6),
% 0.21/0.45    inference(resolution,[],[f74,f29])).
% 0.21/0.45  fof(f74,plain,(
% 0.21/0.45    ~r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) | spl8_6),
% 0.21/0.45    inference(avatar_component_clause,[],[f72])).
% 0.21/0.45  fof(f75,plain,(
% 0.21/0.45    ~spl8_6 | ~spl8_5 | spl8_1),
% 0.21/0.45    inference(avatar_split_clause,[],[f70,f44,f60,f72])).
% 0.21/0.45  fof(f70,plain,(
% 0.21/0.45    ~r2_hidden(sK3,sK7) | ~r2_hidden(k4_tarski(k4_tarski(sK0,sK1),sK2),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) | spl8_1),
% 0.21/0.45    inference(resolution,[],[f29,f46])).
% 0.21/0.45  fof(f46,plain,(
% 0.21/0.45    ~r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) | spl8_1),
% 0.21/0.45    inference(avatar_component_clause,[],[f44])).
% 0.21/0.45  fof(f67,plain,(
% 0.21/0.45    spl8_1 | spl8_2),
% 0.21/0.45    inference(avatar_split_clause,[],[f38,f48,f44])).
% 0.21/0.45  fof(f38,plain,(
% 0.21/0.45    r2_hidden(sK0,sK4) | r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))),
% 0.21/0.45    inference(definition_unfolding,[],[f18,f25,f26])).
% 0.21/0.45  fof(f26,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f5])).
% 0.21/0.45  fof(f5,axiom,(
% 0.21/0.45    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_mcart_1)).
% 0.21/0.45  fof(f25,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f4])).
% 0.21/0.45  fof(f4,axiom,(
% 0.21/0.45    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_mcart_1)).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    r2_hidden(sK0,sK4) | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 0.21/0.45    inference(cnf_transformation,[],[f13])).
% 0.21/0.45  fof(f13,plain,(
% 0.21/0.45    (~r2_hidden(sK3,sK7) | ~r2_hidden(sK2,sK6) | ~r2_hidden(sK1,sK5) | ~r2_hidden(sK0,sK4) | ~r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7))) & ((r2_hidden(sK3,sK7) & r2_hidden(sK2,sK6) & r2_hidden(sK1,sK5) & r2_hidden(sK0,sK4)) | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7)))),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f11,f12])).
% 0.21/0.45  fof(f12,plain,(
% 0.21/0.45    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((~r2_hidden(X3,X7) | ~r2_hidden(X2,X6) | ~r2_hidden(X1,X5) | ~r2_hidden(X0,X4) | ~r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))) & ((r2_hidden(X3,X7) & r2_hidden(X2,X6) & r2_hidden(X1,X5) & r2_hidden(X0,X4)) | r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)))) => ((~r2_hidden(sK3,sK7) | ~r2_hidden(sK2,sK6) | ~r2_hidden(sK1,sK5) | ~r2_hidden(sK0,sK4) | ~r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7))) & ((r2_hidden(sK3,sK7) & r2_hidden(sK2,sK6) & r2_hidden(sK1,sK5) & r2_hidden(sK0,sK4)) | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7))))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f11,plain,(
% 0.21/0.45    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((~r2_hidden(X3,X7) | ~r2_hidden(X2,X6) | ~r2_hidden(X1,X5) | ~r2_hidden(X0,X4) | ~r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))) & ((r2_hidden(X3,X7) & r2_hidden(X2,X6) & r2_hidden(X1,X5) & r2_hidden(X0,X4)) | r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))))),
% 0.21/0.45    inference(flattening,[],[f10])).
% 0.21/0.45  fof(f10,plain,(
% 0.21/0.45    ? [X0,X1,X2,X3,X4,X5,X6,X7] : (((~r2_hidden(X3,X7) | ~r2_hidden(X2,X6) | ~r2_hidden(X1,X5) | ~r2_hidden(X0,X4)) | ~r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))) & ((r2_hidden(X3,X7) & r2_hidden(X2,X6) & r2_hidden(X1,X5) & r2_hidden(X0,X4)) | r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7))))),
% 0.21/0.45    inference(nnf_transformation,[],[f9])).
% 0.21/0.45  fof(f9,plain,(
% 0.21/0.45    ? [X0,X1,X2,X3,X4,X5,X6,X7] : (r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) <~> (r2_hidden(X3,X7) & r2_hidden(X2,X6) & r2_hidden(X1,X5) & r2_hidden(X0,X4)))),
% 0.21/0.45    inference(ennf_transformation,[],[f8])).
% 0.21/0.45  fof(f8,negated_conjecture,(
% 0.21/0.45    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : (r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) <=> (r2_hidden(X3,X7) & r2_hidden(X2,X6) & r2_hidden(X1,X5) & r2_hidden(X0,X4)))),
% 0.21/0.45    inference(negated_conjecture,[],[f7])).
% 0.21/0.45  fof(f7,conjecture,(
% 0.21/0.45    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (r2_hidden(k4_mcart_1(X0,X1,X2,X3),k4_zfmisc_1(X4,X5,X6,X7)) <=> (r2_hidden(X3,X7) & r2_hidden(X2,X6) & r2_hidden(X1,X5) & r2_hidden(X0,X4)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_mcart_1)).
% 0.21/0.45  fof(f66,plain,(
% 0.21/0.45    spl8_1 | spl8_3),
% 0.21/0.45    inference(avatar_split_clause,[],[f37,f52,f44])).
% 0.21/0.45  fof(f37,plain,(
% 0.21/0.45    r2_hidden(sK1,sK5) | r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))),
% 0.21/0.45    inference(definition_unfolding,[],[f19,f25,f26])).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    r2_hidden(sK1,sK5) | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 0.21/0.45    inference(cnf_transformation,[],[f13])).
% 0.21/0.45  fof(f65,plain,(
% 0.21/0.45    spl8_1 | spl8_4),
% 0.21/0.45    inference(avatar_split_clause,[],[f36,f56,f44])).
% 0.21/0.45  fof(f36,plain,(
% 0.21/0.45    r2_hidden(sK2,sK6) | r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))),
% 0.21/0.45    inference(definition_unfolding,[],[f20,f25,f26])).
% 0.21/0.45  fof(f20,plain,(
% 0.21/0.45    r2_hidden(sK2,sK6) | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 0.21/0.45    inference(cnf_transformation,[],[f13])).
% 0.21/0.45  fof(f64,plain,(
% 0.21/0.45    spl8_1 | spl8_5),
% 0.21/0.45    inference(avatar_split_clause,[],[f35,f60,f44])).
% 0.21/0.45  fof(f35,plain,(
% 0.21/0.45    r2_hidden(sK3,sK7) | r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))),
% 0.21/0.45    inference(definition_unfolding,[],[f21,f25,f26])).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    r2_hidden(sK3,sK7) | r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 0.21/0.45    inference(cnf_transformation,[],[f13])).
% 0.21/0.45  fof(f63,plain,(
% 0.21/0.45    ~spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5),
% 0.21/0.45    inference(avatar_split_clause,[],[f34,f60,f56,f52,f48,f44])).
% 0.21/0.45  fof(f34,plain,(
% 0.21/0.45    ~r2_hidden(sK3,sK7) | ~r2_hidden(sK2,sK6) | ~r2_hidden(sK1,sK5) | ~r2_hidden(sK0,sK4) | ~r2_hidden(k4_tarski(k4_tarski(k4_tarski(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))),
% 0.21/0.45    inference(definition_unfolding,[],[f22,f25,f26])).
% 0.21/0.45  fof(f22,plain,(
% 0.21/0.45    ~r2_hidden(sK3,sK7) | ~r2_hidden(sK2,sK6) | ~r2_hidden(sK1,sK5) | ~r2_hidden(sK0,sK4) | ~r2_hidden(k4_mcart_1(sK0,sK1,sK2,sK3),k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 0.21/0.45    inference(cnf_transformation,[],[f13])).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (22032)------------------------------
% 0.21/0.45  % (22032)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (22032)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (22032)Memory used [KB]: 6140
% 0.21/0.45  % (22032)Time elapsed: 0.037 s
% 0.21/0.45  % (22032)------------------------------
% 0.21/0.45  % (22032)------------------------------
% 0.21/0.45  % (22028)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.45  % (22027)Success in time 0.084 s
%------------------------------------------------------------------------------
