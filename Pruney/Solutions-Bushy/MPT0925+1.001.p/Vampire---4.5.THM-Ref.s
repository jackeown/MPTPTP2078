%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0925+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:54 EST 2020

% Result     : Theorem 1.59s
% Output     : Refutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 132 expanded)
%              Number of leaves         :   14 (  46 expanded)
%              Depth                    :   19
%              Number of atoms          :  267 ( 498 expanded)
%              Number of equality atoms :   43 (  98 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f163,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f48,f120,f123,f128,f146,f153,f156,f159,f162])).

fof(f162,plain,
    ( ~ spl17_2
    | spl17_9 ),
    inference(avatar_contradiction_clause,[],[f160])).

fof(f160,plain,
    ( $false
    | ~ spl17_2
    | spl17_9 ),
    inference(unit_resulting_resolution,[],[f103,f145,f10])).

fof(f10,plain,(
    ! [X5] :
      ( r2_hidden(sK5(X5),sK1)
      | ~ r2_hidden(X5,sK0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k4_zfmisc_1(X1,X2,X3,X4) != X0
      & ! [X5] :
          ( r2_hidden(X5,X0)
        <=> ? [X6,X7,X8,X9] :
              ( k4_mcart_1(X6,X7,X8,X9) = X5
              & r2_hidden(X9,X4)
              & r2_hidden(X8,X3)
              & r2_hidden(X7,X2)
              & r2_hidden(X6,X1) ) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( ! [X5] :
            ( r2_hidden(X5,X0)
          <=> ? [X6,X7,X8,X9] :
                ( k4_mcart_1(X6,X7,X8,X9) = X5
                & r2_hidden(X9,X4)
                & r2_hidden(X8,X3)
                & r2_hidden(X7,X2)
                & r2_hidden(X6,X1) ) )
       => k4_zfmisc_1(X1,X2,X3,X4) = X0 ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( ! [X5] :
          ( r2_hidden(X5,X0)
        <=> ? [X6,X7,X8,X9] :
              ( k4_mcart_1(X6,X7,X8,X9) = X5
              & r2_hidden(X9,X4)
              & r2_hidden(X8,X3)
              & r2_hidden(X7,X2)
              & r2_hidden(X6,X1) ) )
     => k4_zfmisc_1(X1,X2,X3,X4) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_mcart_1)).

fof(f145,plain,
    ( ~ r2_hidden(sK5(sK9(k3_zfmisc_1(sK1,sK2,sK3),sK4,sK0)),sK1)
    | spl17_9 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl17_9
  <=> r2_hidden(sK5(sK9(k3_zfmisc_1(sK1,sK2,sK3),sK4,sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_9])])).

fof(f103,plain,
    ( r2_hidden(sK9(k3_zfmisc_1(sK1,sK2,sK3),sK4,sK0),sK0)
    | ~ spl17_2 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl17_2
  <=> r2_hidden(sK9(k3_zfmisc_1(sK1,sK2,sK3),sK4,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_2])])).

fof(f159,plain,
    ( ~ spl17_2
    | spl17_8 ),
    inference(avatar_contradiction_clause,[],[f157])).

fof(f157,plain,
    ( $false
    | ~ spl17_2
    | spl17_8 ),
    inference(unit_resulting_resolution,[],[f103,f141,f12])).

fof(f12,plain,(
    ! [X5] :
      ( r2_hidden(sK7(X5),sK3)
      | ~ r2_hidden(X5,sK0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f141,plain,
    ( ~ r2_hidden(sK7(sK9(k3_zfmisc_1(sK1,sK2,sK3),sK4,sK0)),sK3)
    | spl17_8 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl17_8
  <=> r2_hidden(sK7(sK9(k3_zfmisc_1(sK1,sK2,sK3),sK4,sK0)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_8])])).

fof(f156,plain,
    ( ~ spl17_2
    | spl17_7 ),
    inference(avatar_contradiction_clause,[],[f154])).

fof(f154,plain,
    ( $false
    | ~ spl17_2
    | spl17_7 ),
    inference(unit_resulting_resolution,[],[f103,f137,f11])).

fof(f11,plain,(
    ! [X5] :
      ( r2_hidden(sK6(X5),sK2)
      | ~ r2_hidden(X5,sK0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f137,plain,
    ( ~ r2_hidden(sK6(sK9(k3_zfmisc_1(sK1,sK2,sK3),sK4,sK0)),sK2)
    | spl17_7 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl17_7
  <=> r2_hidden(sK6(sK9(k3_zfmisc_1(sK1,sK2,sK3),sK4,sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_7])])).

fof(f153,plain,
    ( ~ spl17_2
    | spl17_6 ),
    inference(avatar_contradiction_clause,[],[f151])).

fof(f151,plain,
    ( $false
    | ~ spl17_2
    | spl17_6 ),
    inference(unit_resulting_resolution,[],[f103,f133,f13])).

fof(f13,plain,(
    ! [X5] :
      ( r2_hidden(sK8(X5),sK4)
      | ~ r2_hidden(X5,sK0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f133,plain,
    ( ~ r2_hidden(sK8(sK9(k3_zfmisc_1(sK1,sK2,sK3),sK4,sK0)),sK4)
    | spl17_6 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl17_6
  <=> r2_hidden(sK8(sK9(k3_zfmisc_1(sK1,sK2,sK3),sK4,sK0)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_6])])).

fof(f146,plain,
    ( ~ spl17_6
    | ~ spl17_2
    | ~ spl17_7
    | ~ spl17_8
    | ~ spl17_9
    | ~ spl17_5 ),
    inference(avatar_split_clause,[],[f129,f126,f143,f139,f135,f101,f131])).

fof(f126,plain,
    ( spl17_5
  <=> ! [X0] :
        ( sK9(k3_zfmisc_1(sK1,sK2,sK3),sK4,sK0) != X0
        | ~ r2_hidden(sK5(X0),sK1)
        | ~ r2_hidden(sK7(X0),sK3)
        | ~ r2_hidden(sK6(X0),sK2)
        | ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(sK8(X0),sK4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_5])])).

fof(f129,plain,
    ( ~ r2_hidden(sK5(sK9(k3_zfmisc_1(sK1,sK2,sK3),sK4,sK0)),sK1)
    | ~ r2_hidden(sK7(sK9(k3_zfmisc_1(sK1,sK2,sK3),sK4,sK0)),sK3)
    | ~ r2_hidden(sK6(sK9(k3_zfmisc_1(sK1,sK2,sK3),sK4,sK0)),sK2)
    | ~ r2_hidden(sK9(k3_zfmisc_1(sK1,sK2,sK3),sK4,sK0),sK0)
    | ~ r2_hidden(sK8(sK9(k3_zfmisc_1(sK1,sK2,sK3),sK4,sK0)),sK4)
    | ~ spl17_5 ),
    inference(equality_resolution,[],[f127])).

fof(f127,plain,
    ( ! [X0] :
        ( sK9(k3_zfmisc_1(sK1,sK2,sK3),sK4,sK0) != X0
        | ~ r2_hidden(sK5(X0),sK1)
        | ~ r2_hidden(sK7(X0),sK3)
        | ~ r2_hidden(sK6(X0),sK2)
        | ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(sK8(X0),sK4) )
    | ~ spl17_5 ),
    inference(avatar_component_clause,[],[f126])).

fof(f128,plain,
    ( spl17_1
    | spl17_5
    | ~ spl17_2 ),
    inference(avatar_split_clause,[],[f124,f101,f126,f45])).

fof(f45,plain,
    ( spl17_1
  <=> sK0 = k2_zfmisc_1(k3_zfmisc_1(sK1,sK2,sK3),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_1])])).

fof(f124,plain,
    ( ! [X0] :
        ( sK9(k3_zfmisc_1(sK1,sK2,sK3),sK4,sK0) != X0
        | ~ r2_hidden(sK8(X0),sK4)
        | sK0 = k2_zfmisc_1(k3_zfmisc_1(sK1,sK2,sK3),sK4)
        | ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(sK6(X0),sK2)
        | ~ r2_hidden(sK7(X0),sK3)
        | ~ r2_hidden(sK5(X0),sK1) )
    | ~ spl17_2 ),
    inference(resolution,[],[f103,f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(sK9(k3_zfmisc_1(X2,X3,X4),X1,X5),X5)
      | sK9(k3_zfmisc_1(X2,X3,X4),X1,X5) != X0
      | ~ r2_hidden(sK8(X0),X1)
      | k2_zfmisc_1(k3_zfmisc_1(X2,X3,X4),X1) = X5
      | ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(sK6(X0),X3)
      | ~ r2_hidden(sK7(X0),X4)
      | ~ r2_hidden(sK5(X0),X2) ) ),
    inference(resolution,[],[f49,f34])).

fof(f34,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))
      | ~ r2_hidden(X1,X4)
      | ~ r2_hidden(X2,X5)
      | ~ r2_hidden(X0,X3) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( r2_hidden(k3_mcart_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))
    <=> ( r2_hidden(X2,X5)
        & r2_hidden(X1,X4)
        & r2_hidden(X0,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_mcart_1)).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k3_mcart_1(sK5(X0),sK6(X0),sK7(X0)),X1)
      | ~ r2_hidden(sK8(X0),X2)
      | sK9(X1,X2,X3) != X0
      | ~ r2_hidden(sK9(X1,X2,X3),X3)
      | k2_zfmisc_1(X1,X2) = X3
      | ~ r2_hidden(X0,sK0) ) ),
    inference(superposition,[],[f17,f37])).

fof(f37,plain,(
    ! [X5] :
      ( k4_tarski(k3_mcart_1(sK5(X5),sK6(X5),sK7(X5)),sK8(X5)) = X5
      | ~ r2_hidden(X5,sK0) ) ),
    inference(definition_unfolding,[],[f14,f25])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).

fof(f14,plain,(
    ! [X5] :
      ( k4_mcart_1(sK5(X5),sK6(X5),sK7(X5),sK8(X5)) = X5
      | ~ r2_hidden(X5,sK0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f17,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( k4_tarski(X4,X5) != sK9(X0,X1,X2)
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X0)
      | ~ r2_hidden(sK9(X0,X1,X2),X2)
      | k2_zfmisc_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f123,plain,
    ( spl17_1
    | spl17_2
    | spl17_4 ),
    inference(avatar_contradiction_clause,[],[f121])).

fof(f121,plain,
    ( $false
    | spl17_1
    | spl17_2
    | spl17_4 ),
    inference(unit_resulting_resolution,[],[f47,f102,f119,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK13(X0,X1,X2),X1)
      | r2_hidden(sK9(X0,X1,X2),X2)
      | k2_zfmisc_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f119,plain,
    ( ~ r2_hidden(sK13(k3_zfmisc_1(sK1,sK2,sK3),sK4,sK0),sK4)
    | spl17_4 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl17_4
  <=> r2_hidden(sK13(k3_zfmisc_1(sK1,sK2,sK3),sK4,sK0),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_4])])).

fof(f102,plain,
    ( ~ r2_hidden(sK9(k3_zfmisc_1(sK1,sK2,sK3),sK4,sK0),sK0)
    | spl17_2 ),
    inference(avatar_component_clause,[],[f101])).

fof(f47,plain,
    ( sK0 != k2_zfmisc_1(k3_zfmisc_1(sK1,sK2,sK3),sK4)
    | spl17_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f120,plain,
    ( spl17_1
    | ~ spl17_4
    | spl17_2 ),
    inference(avatar_split_clause,[],[f110,f101,f117,f45])).

fof(f110,plain,
    ( ~ r2_hidden(sK13(k3_zfmisc_1(sK1,sK2,sK3),sK4,sK0),sK4)
    | sK0 = k2_zfmisc_1(k3_zfmisc_1(sK1,sK2,sK3),sK4)
    | spl17_2 ),
    inference(resolution,[],[f102,f93])).

fof(f93,plain,(
    ! [X0] :
      ( r2_hidden(sK9(k3_zfmisc_1(sK1,sK2,sK3),X0,sK0),sK0)
      | ~ r2_hidden(sK13(k3_zfmisc_1(sK1,sK2,sK3),X0,sK0),sK4)
      | sK0 = k2_zfmisc_1(k3_zfmisc_1(sK1,sK2,sK3),X0) ) ),
    inference(factoring,[],[f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK9(k3_zfmisc_1(sK1,sK2,sK3),X0,X1),sK0)
      | ~ r2_hidden(sK13(k3_zfmisc_1(sK1,sK2,sK3),X0,X1),sK4)
      | r2_hidden(sK9(k3_zfmisc_1(sK1,sK2,sK3),X0,X1),X1)
      | k2_zfmisc_1(k3_zfmisc_1(sK1,sK2,sK3),X0) = X1 ) ),
    inference(duplicate_literal_removal,[],[f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK9(k3_zfmisc_1(sK1,sK2,sK3),X0,X1),sK0)
      | ~ r2_hidden(sK13(k3_zfmisc_1(sK1,sK2,sK3),X0,X1),sK4)
      | r2_hidden(sK9(k3_zfmisc_1(sK1,sK2,sK3),X0,X1),X1)
      | k2_zfmisc_1(k3_zfmisc_1(sK1,sK2,sK3),X0) = X1
      | r2_hidden(sK9(k3_zfmisc_1(sK1,sK2,sK3),X0,X1),X1)
      | k2_zfmisc_1(k3_zfmisc_1(sK1,sK2,sK3),X0) = X1 ) ),
    inference(superposition,[],[f66,f20])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( sK9(X0,X1,X2) = k4_tarski(sK12(X0,X1,X2),sK13(X0,X1,X2))
      | r2_hidden(sK9(X0,X1,X2),X2)
      | k2_zfmisc_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f66,plain,(
    ! [X12,X10,X11] :
      ( r2_hidden(k4_tarski(sK12(k3_zfmisc_1(sK1,sK2,sK3),X10,X11),X12),sK0)
      | ~ r2_hidden(X12,sK4)
      | r2_hidden(sK9(k3_zfmisc_1(sK1,sK2,sK3),X10,X11),X11)
      | k2_zfmisc_1(k3_zfmisc_1(sK1,sK2,sK3),X10) = X11 ) ),
    inference(resolution,[],[f62,f18])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK12(X0,X1,X2),X0)
      | r2_hidden(sK9(X0,X1,X2),X2)
      | k2_zfmisc_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k3_zfmisc_1(sK1,sK2,sK3))
      | r2_hidden(k4_tarski(X1,X0),sK0)
      | ~ r2_hidden(X0,sK4) ) ),
    inference(duplicate_literal_removal,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK4)
      | r2_hidden(k4_tarski(X1,X0),sK0)
      | ~ r2_hidden(X1,k3_zfmisc_1(sK1,sK2,sK3))
      | ~ r2_hidden(X1,k3_zfmisc_1(sK1,sK2,sK3)) ) ),
    inference(resolution,[],[f60,f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK14(X0,X1,X2,X3),X1)
      | ~ r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4,X5,X6] :
          ( k3_mcart_1(X4,X5,X6) = X0
          & r2_hidden(X6,X3)
          & r2_hidden(X5,X2)
          & r2_hidden(X4,X1) )
      | ~ r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ! [X4,X5,X6] :
            ~ ( k3_mcart_1(X4,X5,X6) = X0
              & r2_hidden(X6,X3)
              & r2_hidden(X5,X2)
              & r2_hidden(X4,X1) )
        & r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_mcart_1)).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK14(X0,X2,sK2,sK3),sK1)
      | ~ r2_hidden(X1,sK4)
      | r2_hidden(k4_tarski(X0,X1),sK0)
      | ~ r2_hidden(X0,k3_zfmisc_1(X2,sK2,sK3)) ) ),
    inference(duplicate_literal_removal,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),sK0)
      | ~ r2_hidden(X1,sK4)
      | ~ r2_hidden(sK14(X0,X2,sK2,sK3),sK1)
      | ~ r2_hidden(X0,k3_zfmisc_1(X2,sK2,sK3))
      | ~ r2_hidden(X0,k3_zfmisc_1(X2,sK2,sK3)) ) ),
    inference(resolution,[],[f58,f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK15(X0,X1,X2,X3),X2)
      | ~ r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK15(X0,X1,X2,sK3),sK2)
      | r2_hidden(k4_tarski(X0,X3),sK0)
      | ~ r2_hidden(X3,sK4)
      | ~ r2_hidden(sK14(X0,X1,X2,sK3),sK1)
      | ~ r2_hidden(X0,k3_zfmisc_1(X1,X2,sK3)) ) ),
    inference(duplicate_literal_removal,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK15(X0,X1,X2,sK3),sK2)
      | r2_hidden(k4_tarski(X0,X3),sK0)
      | ~ r2_hidden(X3,sK4)
      | ~ r2_hidden(sK14(X0,X1,X2,sK3),sK1)
      | ~ r2_hidden(X0,k3_zfmisc_1(X1,X2,sK3))
      | ~ r2_hidden(X0,k3_zfmisc_1(X1,X2,sK3)) ) ),
    inference(resolution,[],[f51,f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK16(X0,X1,X2,X3),X3)
      | ~ r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(sK16(X0,X1,X2,X3),sK3)
      | ~ r2_hidden(sK15(X0,X1,X2,X3),sK2)
      | r2_hidden(k4_tarski(X0,X4),sK0)
      | ~ r2_hidden(X4,sK4)
      | ~ r2_hidden(sK14(X0,X1,X2,X3),sK1)
      | ~ r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) ) ),
    inference(superposition,[],[f38,f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_mcart_1(sK14(X0,X1,X2,X3),sK15(X0,X1,X2,X3),sK16(X0,X1,X2,X3)) = X0
      | ~ r2_hidden(X0,k3_zfmisc_1(X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f38,plain,(
    ! [X6,X8,X7,X9] :
      ( r2_hidden(k4_tarski(k3_mcart_1(X6,X7,X8),X9),sK0)
      | ~ r2_hidden(X7,sK2)
      | ~ r2_hidden(X8,sK3)
      | ~ r2_hidden(X9,sK4)
      | ~ r2_hidden(X6,sK1) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( ~ r2_hidden(X6,sK1)
      | ~ r2_hidden(X7,sK2)
      | ~ r2_hidden(X8,sK3)
      | ~ r2_hidden(X9,sK4)
      | k4_tarski(k3_mcart_1(X6,X7,X8),X9) != X5
      | r2_hidden(X5,sK0) ) ),
    inference(definition_unfolding,[],[f15,f25])).

fof(f15,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( ~ r2_hidden(X6,sK1)
      | ~ r2_hidden(X7,sK2)
      | ~ r2_hidden(X8,sK3)
      | ~ r2_hidden(X9,sK4)
      | k4_mcart_1(X6,X7,X8,X9) != X5
      | r2_hidden(X5,sK0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f48,plain,(
    ~ spl17_1 ),
    inference(avatar_split_clause,[],[f35,f45])).

fof(f35,plain,(
    sK0 != k2_zfmisc_1(k3_zfmisc_1(sK1,sK2,sK3),sK4) ),
    inference(definition_unfolding,[],[f16,f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f16,plain,(
    sK0 != k4_zfmisc_1(sK1,sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f8])).

%------------------------------------------------------------------------------
