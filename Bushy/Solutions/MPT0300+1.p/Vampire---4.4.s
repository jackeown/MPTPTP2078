%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : zfmisc_1__t108_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:57 EDT 2019

% Result     : Theorem 0.74s
% Output     : Refutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :  177 ( 450 expanded)
%              Number of leaves         :   43 ( 174 expanded)
%              Depth                    :    9
%              Number of atoms          :  440 (1122 expanded)
%              Number of equality atoms :   46 ( 198 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f457,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f62,f87,f92,f108,f112,f139,f157,f177,f212,f219,f232,f239,f246,f260,f267,f282,f290,f294,f309,f314,f325,f334,f356,f361,f364,f377,f382,f387,f394,f403,f404,f411,f412,f425,f452])).

fof(f452,plain,
    ( ~ spl10_6
    | spl10_9
    | ~ spl10_50 ),
    inference(avatar_contradiction_clause,[],[f451])).

fof(f451,plain,
    ( $false
    | ~ spl10_6
    | ~ spl10_9
    | ~ spl10_50 ),
    inference(subsumption_resolution,[],[f450,f77])).

fof(f77,plain,
    ( r2_hidden(sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK0,sK1))
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl10_6
  <=> r2_hidden(sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f450,plain,
    ( ~ r2_hidden(sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK0,sK1))
    | ~ spl10_9
    | ~ spl10_50 ),
    inference(forward_demodulation,[],[f449,f333])).

fof(f333,plain,
    ( k4_tarski(sK5(sK0,sK1,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),sK6(sK0,sK1,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))) = sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | ~ spl10_50 ),
    inference(avatar_component_clause,[],[f332])).

fof(f332,plain,
    ( spl10_50
  <=> k4_tarski(sK5(sK0,sK1,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),sK6(sK0,sK1,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))) = sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_50])])).

fof(f449,plain,
    ( ~ r2_hidden(k4_tarski(sK5(sK0,sK1,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),sK6(sK0,sK1,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))),k2_zfmisc_1(sK0,sK1))
    | ~ spl10_9
    | ~ spl10_50 ),
    inference(subsumption_resolution,[],[f440,f86])).

fof(f86,plain,
    ( ~ r2_hidden(sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK2,sK3))
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl10_9
  <=> ~ r2_hidden(sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f440,plain,
    ( r2_hidden(sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK2,sK3))
    | ~ r2_hidden(k4_tarski(sK5(sK0,sK1,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),sK6(sK0,sK1,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))),k2_zfmisc_1(sK0,sK1))
    | ~ spl10_50 ),
    inference(superposition,[],[f20,f333])).

fof(f20,plain,(
    ! [X4,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK2,sK3))
      | ~ r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK0,sK1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3)
      & ! [X4,X5] :
          ( r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1))
        <=> r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ! [X4,X5] :
            ( r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1))
          <=> r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X2,X3)) )
       => k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ! [X4,X5] :
          ( r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1))
        <=> r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X2,X3)) )
     => k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t108_zfmisc_1.p',t108_zfmisc_1)).

fof(f425,plain,
    ( spl10_7
    | ~ spl10_8
    | ~ spl10_24 ),
    inference(avatar_contradiction_clause,[],[f424])).

fof(f424,plain,
    ( $false
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_24 ),
    inference(subsumption_resolution,[],[f423,f80])).

fof(f80,plain,
    ( ~ r2_hidden(sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK0,sK1))
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl10_7
  <=> ~ r2_hidden(sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f423,plain,
    ( r2_hidden(sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK0,sK1))
    | ~ spl10_8
    | ~ spl10_24 ),
    inference(forward_demodulation,[],[f422,f211])).

fof(f211,plain,
    ( k4_tarski(sK5(sK2,sK3,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),sK6(sK2,sK3,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))) = sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | ~ spl10_24 ),
    inference(avatar_component_clause,[],[f210])).

fof(f210,plain,
    ( spl10_24
  <=> k4_tarski(sK5(sK2,sK3,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),sK6(sK2,sK3,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))) = sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_24])])).

fof(f422,plain,
    ( r2_hidden(k4_tarski(sK5(sK2,sK3,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),sK6(sK2,sK3,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))),k2_zfmisc_1(sK0,sK1))
    | ~ spl10_8
    | ~ spl10_24 ),
    inference(subsumption_resolution,[],[f413,f83])).

fof(f83,plain,
    ( r2_hidden(sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK2,sK3))
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl10_8
  <=> r2_hidden(sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f413,plain,
    ( ~ r2_hidden(sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK2,sK3))
    | r2_hidden(k4_tarski(sK5(sK2,sK3,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),sK6(sK2,sK3,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))),k2_zfmisc_1(sK0,sK1))
    | ~ spl10_24 ),
    inference(superposition,[],[f19,f211])).

fof(f19,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK2,sK3))
      | r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(sK0,sK1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f412,plain,
    ( spl10_2
    | ~ spl10_31 ),
    inference(avatar_split_clause,[],[f192,f237,f54])).

fof(f54,plain,
    ( spl10_2
  <=> ! [X1,X0] : ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f237,plain,
    ( spl10_31
  <=> ~ v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_31])])).

fof(f192,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(sK2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1)) ) ),
    inference(resolution,[],[f64,f20])).

fof(f64,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X3,k2_zfmisc_1(X4,X5))
      | ~ v1_xboole_0(X4) ) ),
    inference(resolution,[],[f40,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t108_zfmisc_1.p',t7_boole)).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK5(X0,X1,X3),X0)
      | ~ r2_hidden(X3,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK5(X0,X1,X3),X0)
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t108_zfmisc_1.p',d2_zfmisc_1)).

fof(f411,plain,
    ( spl10_24
    | spl10_45
    | spl10_47 ),
    inference(avatar_split_clause,[],[f312,f307,f301,f210])).

fof(f301,plain,
    ( spl10_45
  <=> ~ r2_hidden(sK9(sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)),k4_tarski(sK5(sK2,sK3,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),sK6(sK2,sK3,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))))),sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_45])])).

fof(f307,plain,
    ( spl10_47
  <=> ~ r2_hidden(sK9(sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)),k4_tarski(sK5(sK2,sK3,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),sK6(sK2,sK3,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))))),k4_tarski(sK5(sK2,sK3,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),sK6(sK2,sK3,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_47])])).

fof(f312,plain,
    ( k4_tarski(sK5(sK2,sK3,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),sK6(sK2,sK3,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))) = sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | ~ spl10_45
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f311,f302])).

fof(f302,plain,
    ( ~ r2_hidden(sK9(sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)),k4_tarski(sK5(sK2,sK3,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),sK6(sK2,sK3,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))))),sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))
    | ~ spl10_45 ),
    inference(avatar_component_clause,[],[f301])).

fof(f311,plain,
    ( r2_hidden(sK9(sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)),k4_tarski(sK5(sK2,sK3,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),sK6(sK2,sK3,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))))),sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))
    | k4_tarski(sK5(sK2,sK3,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),sK6(sK2,sK3,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))) = sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | ~ spl10_47 ),
    inference(resolution,[],[f308,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK9(X0,X1),X1)
      | r2_hidden(sK9(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t108_zfmisc_1.p',t2_tarski)).

fof(f308,plain,
    ( ~ r2_hidden(sK9(sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)),k4_tarski(sK5(sK2,sK3,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),sK6(sK2,sK3,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))))),k4_tarski(sK5(sK2,sK3,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),sK6(sK2,sK3,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))))
    | ~ spl10_47 ),
    inference(avatar_component_clause,[],[f307])).

fof(f404,plain,
    ( spl10_2
    | ~ spl10_27 ),
    inference(avatar_split_clause,[],[f178,f217,f54])).

fof(f217,plain,
    ( spl10_27
  <=> ~ v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_27])])).

fof(f178,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(sK3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1)) ) ),
    inference(resolution,[],[f52,f20])).

fof(f52,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X3,k2_zfmisc_1(X4,X5))
      | ~ v1_xboole_0(X5) ) ),
    inference(resolution,[],[f39,f34])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK6(X0,X1,X3),X1)
      | ~ r2_hidden(X3,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK6(X0,X1,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f403,plain,
    ( spl10_62
    | ~ spl10_12 ),
    inference(avatar_split_clause,[],[f251,f103,f401])).

fof(f401,plain,
    ( spl10_62
  <=> k4_tarski(sK5(sK0,sK1,sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))),sK6(sK0,sK1,sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)))) = sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_62])])).

fof(f103,plain,
    ( spl10_12
  <=> r2_hidden(sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f251,plain,
    ( k4_tarski(sK5(sK0,sK1,sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))),sK6(sK0,sK1,sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)))) = sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))
    | ~ spl10_12 ),
    inference(resolution,[],[f104,f38])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_zfmisc_1(X0,X1))
      | k4_tarski(sK5(X0,X1,X3),sK6(X0,X1,X3)) = X3 ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(sK5(X0,X1,X3),sK6(X0,X1,X3)) = X3
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f104,plain,
    ( r2_hidden(sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f103])).

fof(f394,plain,
    ( ~ spl10_61
    | spl10_55
    | spl10_57
    | spl10_59 ),
    inference(avatar_split_clause,[],[f383,f375,f369,f354,f392])).

fof(f392,plain,
    ( spl10_61
  <=> ~ r2_hidden(sK9(sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)),sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))),sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_61])])).

fof(f354,plain,
    ( spl10_55
  <=> ~ r2_hidden(sK9(k4_tarski(sK5(sK2,sK3,sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))),sK6(sK2,sK3,sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)))),sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))),sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_55])])).

fof(f369,plain,
    ( spl10_57
  <=> ~ r2_hidden(sK9(sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)),k4_tarski(sK5(sK2,sK3,sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))),sK6(sK2,sK3,sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))))),sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_57])])).

fof(f375,plain,
    ( spl10_59
  <=> ~ r2_hidden(sK9(sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)),k4_tarski(sK5(sK2,sK3,sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))),sK6(sK2,sK3,sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))))),k4_tarski(sK5(sK2,sK3,sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))),sK6(sK2,sK3,sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_59])])).

fof(f383,plain,
    ( ~ r2_hidden(sK9(sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)),sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))),sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)))
    | ~ spl10_55
    | ~ spl10_57
    | ~ spl10_59 ),
    inference(backward_demodulation,[],[f380,f355])).

fof(f355,plain,
    ( ~ r2_hidden(sK9(k4_tarski(sK5(sK2,sK3,sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))),sK6(sK2,sK3,sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)))),sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))),sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)))
    | ~ spl10_55 ),
    inference(avatar_component_clause,[],[f354])).

fof(f380,plain,
    ( k4_tarski(sK5(sK2,sK3,sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))),sK6(sK2,sK3,sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)))) = sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))
    | ~ spl10_57
    | ~ spl10_59 ),
    inference(subsumption_resolution,[],[f379,f370])).

fof(f370,plain,
    ( ~ r2_hidden(sK9(sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)),k4_tarski(sK5(sK2,sK3,sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))),sK6(sK2,sK3,sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))))),sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)))
    | ~ spl10_57 ),
    inference(avatar_component_clause,[],[f369])).

fof(f379,plain,
    ( r2_hidden(sK9(sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)),k4_tarski(sK5(sK2,sK3,sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))),sK6(sK2,sK3,sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))))),sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)))
    | k4_tarski(sK5(sK2,sK3,sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))),sK6(sK2,sK3,sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)))) = sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))
    | ~ spl10_59 ),
    inference(resolution,[],[f376,f31])).

fof(f376,plain,
    ( ~ r2_hidden(sK9(sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)),k4_tarski(sK5(sK2,sK3,sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))),sK6(sK2,sK3,sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))))),k4_tarski(sK5(sK2,sK3,sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))),sK6(sK2,sK3,sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)))))
    | ~ spl10_59 ),
    inference(avatar_component_clause,[],[f375])).

fof(f387,plain,
    ( spl10_20
    | spl10_22
    | ~ spl10_37 ),
    inference(avatar_split_clause,[],[f194,f265,f175,f172])).

fof(f172,plain,
    ( spl10_20
  <=> ! [X5] : ~ r2_hidden(X5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).

fof(f175,plain,
    ( spl10_22
  <=> ! [X4] : ~ r2_hidden(X4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).

fof(f265,plain,
    ( spl10_37
  <=> ~ v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_37])])).

fof(f194,plain,(
    ! [X6,X7] :
      ( ~ v1_xboole_0(sK0)
      | ~ r2_hidden(X6,sK2)
      | ~ r2_hidden(X7,sK3) ) ),
    inference(resolution,[],[f64,f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(X1,sK2)
      | ~ r2_hidden(X0,sK3) ) ),
    inference(resolution,[],[f37,f19])).

fof(f37,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | r2_hidden(k4_tarski(X4,X5),X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | k4_tarski(X4,X5) != X3
      | r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f382,plain,
    ( spl10_33
    | spl10_57
    | spl10_59 ),
    inference(avatar_contradiction_clause,[],[f381])).

fof(f381,plain,
    ( $false
    | ~ spl10_33
    | ~ spl10_57
    | ~ spl10_59 ),
    inference(subsumption_resolution,[],[f380,f242])).

fof(f242,plain,
    ( k4_tarski(sK5(sK2,sK3,sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))),sK6(sK2,sK3,sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)))) != sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))
    | ~ spl10_33 ),
    inference(avatar_component_clause,[],[f241])).

fof(f241,plain,
    ( spl10_33
  <=> k4_tarski(sK5(sK2,sK3,sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))),sK6(sK2,sK3,sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)))) != sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_33])])).

fof(f377,plain,
    ( ~ spl10_57
    | ~ spl10_59
    | spl10_33 ),
    inference(avatar_split_clause,[],[f343,f241,f375,f369])).

fof(f343,plain,
    ( ~ r2_hidden(sK9(sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)),k4_tarski(sK5(sK2,sK3,sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))),sK6(sK2,sK3,sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))))),k4_tarski(sK5(sK2,sK3,sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))),sK6(sK2,sK3,sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)))))
    | ~ r2_hidden(sK9(sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)),k4_tarski(sK5(sK2,sK3,sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))),sK6(sK2,sK3,sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))))),sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)))
    | ~ spl10_33 ),
    inference(extensionality_resolution,[],[f32,f242])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK9(X0,X1),X1)
      | ~ r2_hidden(sK9(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f364,plain,
    ( spl10_20
    | spl10_22
    | ~ spl10_43 ),
    inference(avatar_split_clause,[],[f180,f288,f175,f172])).

fof(f288,plain,
    ( spl10_43
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_43])])).

fof(f180,plain,(
    ! [X6,X7] :
      ( ~ v1_xboole_0(sK1)
      | ~ r2_hidden(X6,sK2)
      | ~ r2_hidden(X7,sK3) ) ),
    inference(resolution,[],[f52,f116])).

fof(f361,plain,
    ( spl10_33
    | spl10_53
    | spl10_55 ),
    inference(avatar_contradiction_clause,[],[f360])).

fof(f360,plain,
    ( $false
    | ~ spl10_33
    | ~ spl10_53
    | ~ spl10_55 ),
    inference(subsumption_resolution,[],[f359,f242])).

fof(f359,plain,
    ( k4_tarski(sK5(sK2,sK3,sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))),sK6(sK2,sK3,sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)))) = sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))
    | ~ spl10_53
    | ~ spl10_55 ),
    inference(subsumption_resolution,[],[f358,f355])).

fof(f358,plain,
    ( r2_hidden(sK9(k4_tarski(sK5(sK2,sK3,sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))),sK6(sK2,sK3,sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)))),sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))),sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)))
    | k4_tarski(sK5(sK2,sK3,sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))),sK6(sK2,sK3,sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)))) = sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))
    | ~ spl10_53 ),
    inference(resolution,[],[f349,f31])).

fof(f349,plain,
    ( ~ r2_hidden(sK9(k4_tarski(sK5(sK2,sK3,sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))),sK6(sK2,sK3,sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)))),sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))),k4_tarski(sK5(sK2,sK3,sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))),sK6(sK2,sK3,sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)))))
    | ~ spl10_53 ),
    inference(avatar_component_clause,[],[f348])).

fof(f348,plain,
    ( spl10_53
  <=> ~ r2_hidden(sK9(k4_tarski(sK5(sK2,sK3,sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))),sK6(sK2,sK3,sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)))),sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))),k4_tarski(sK5(sK2,sK3,sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))),sK6(sK2,sK3,sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_53])])).

fof(f356,plain,
    ( ~ spl10_53
    | ~ spl10_55
    | spl10_33 ),
    inference(avatar_split_clause,[],[f342,f241,f354,f348])).

fof(f342,plain,
    ( ~ r2_hidden(sK9(k4_tarski(sK5(sK2,sK3,sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))),sK6(sK2,sK3,sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)))),sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))),sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)))
    | ~ r2_hidden(sK9(k4_tarski(sK5(sK2,sK3,sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))),sK6(sK2,sK3,sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)))),sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))),k4_tarski(sK5(sK2,sK3,sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))),sK6(sK2,sK3,sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)))))
    | ~ spl10_33 ),
    inference(extensionality_resolution,[],[f32,f242])).

fof(f334,plain,
    ( spl10_50
    | ~ spl10_6 ),
    inference(avatar_split_clause,[],[f222,f76,f332])).

fof(f222,plain,
    ( k4_tarski(sK5(sK0,sK1,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),sK6(sK0,sK1,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))) = sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | ~ spl10_6 ),
    inference(resolution,[],[f77,f38])).

fof(f325,plain,
    ( ~ spl10_49
    | spl10_41
    | spl10_45
    | spl10_47 ),
    inference(avatar_split_clause,[],[f315,f307,f301,f280,f323])).

fof(f323,plain,
    ( spl10_49
  <=> ~ r2_hidden(sK9(sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)),sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_49])])).

fof(f280,plain,
    ( spl10_41
  <=> ~ r2_hidden(sK9(k4_tarski(sK5(sK2,sK3,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),sK6(sK2,sK3,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))),sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_41])])).

fof(f315,plain,
    ( ~ r2_hidden(sK9(sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)),sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))
    | ~ spl10_41
    | ~ spl10_45
    | ~ spl10_47 ),
    inference(backward_demodulation,[],[f312,f281])).

fof(f281,plain,
    ( ~ r2_hidden(sK9(k4_tarski(sK5(sK2,sK3,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),sK6(sK2,sK3,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))),sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))
    | ~ spl10_41 ),
    inference(avatar_component_clause,[],[f280])).

fof(f314,plain,
    ( spl10_25
    | spl10_45
    | spl10_47 ),
    inference(avatar_contradiction_clause,[],[f313])).

fof(f313,plain,
    ( $false
    | ~ spl10_25
    | ~ spl10_45
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f312,f208])).

fof(f208,plain,
    ( k4_tarski(sK5(sK2,sK3,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),sK6(sK2,sK3,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))) != sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | ~ spl10_25 ),
    inference(avatar_component_clause,[],[f207])).

fof(f207,plain,
    ( spl10_25
  <=> k4_tarski(sK5(sK2,sK3,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),sK6(sK2,sK3,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))) != sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_25])])).

fof(f309,plain,
    ( ~ spl10_45
    | ~ spl10_47
    | spl10_25 ),
    inference(avatar_split_clause,[],[f269,f207,f307,f301])).

fof(f269,plain,
    ( ~ r2_hidden(sK9(sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)),k4_tarski(sK5(sK2,sK3,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),sK6(sK2,sK3,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))))),k4_tarski(sK5(sK2,sK3,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),sK6(sK2,sK3,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))))
    | ~ r2_hidden(sK9(sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)),k4_tarski(sK5(sK2,sK3,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),sK6(sK2,sK3,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))))),sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))
    | ~ spl10_25 ),
    inference(extensionality_resolution,[],[f32,f208])).

fof(f294,plain,
    ( spl10_25
    | spl10_39
    | spl10_41 ),
    inference(avatar_contradiction_clause,[],[f293])).

fof(f293,plain,
    ( $false
    | ~ spl10_25
    | ~ spl10_39
    | ~ spl10_41 ),
    inference(subsumption_resolution,[],[f292,f208])).

fof(f292,plain,
    ( k4_tarski(sK5(sK2,sK3,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),sK6(sK2,sK3,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))) = sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | ~ spl10_39
    | ~ spl10_41 ),
    inference(subsumption_resolution,[],[f291,f281])).

fof(f291,plain,
    ( r2_hidden(sK9(k4_tarski(sK5(sK2,sK3,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),sK6(sK2,sK3,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))),sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))
    | k4_tarski(sK5(sK2,sK3,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),sK6(sK2,sK3,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))) = sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | ~ spl10_39 ),
    inference(resolution,[],[f275,f31])).

fof(f275,plain,
    ( ~ r2_hidden(sK9(k4_tarski(sK5(sK2,sK3,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),sK6(sK2,sK3,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))),sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),k4_tarski(sK5(sK2,sK3,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),sK6(sK2,sK3,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))))
    | ~ spl10_39 ),
    inference(avatar_component_clause,[],[f274])).

fof(f274,plain,
    ( spl10_39
  <=> ~ r2_hidden(sK9(k4_tarski(sK5(sK2,sK3,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),sK6(sK2,sK3,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))),sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),k4_tarski(sK5(sK2,sK3,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),sK6(sK2,sK3,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_39])])).

fof(f290,plain,
    ( ~ spl10_43
    | ~ spl10_6 ),
    inference(avatar_split_clause,[],[f221,f76,f288])).

fof(f221,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl10_6 ),
    inference(resolution,[],[f77,f52])).

fof(f282,plain,
    ( ~ spl10_39
    | ~ spl10_41
    | spl10_25 ),
    inference(avatar_split_clause,[],[f268,f207,f280,f274])).

fof(f268,plain,
    ( ~ r2_hidden(sK9(k4_tarski(sK5(sK2,sK3,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),sK6(sK2,sK3,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))),sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))
    | ~ r2_hidden(sK9(k4_tarski(sK5(sK2,sK3,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),sK6(sK2,sK3,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))),sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),k4_tarski(sK5(sK2,sK3,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),sK6(sK2,sK3,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))))
    | ~ spl10_25 ),
    inference(extensionality_resolution,[],[f32,f208])).

fof(f267,plain,
    ( ~ spl10_37
    | ~ spl10_6 ),
    inference(avatar_split_clause,[],[f220,f76,f265])).

fof(f220,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl10_6 ),
    inference(resolution,[],[f77,f64])).

fof(f260,plain,
    ( ~ spl10_35
    | ~ spl10_12 ),
    inference(avatar_split_clause,[],[f252,f103,f258])).

fof(f258,plain,
    ( spl10_35
  <=> ~ r2_hidden(k2_zfmisc_1(sK0,sK1),sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_35])])).

fof(f252,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK0,sK1),sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)))
    | ~ spl10_12 ),
    inference(resolution,[],[f104,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t108_zfmisc_1.p',antisymmetry_r2_hidden)).

fof(f246,plain,
    ( spl10_32
    | ~ spl10_10 ),
    inference(avatar_split_clause,[],[f126,f97,f244])).

fof(f244,plain,
    ( spl10_32
  <=> k4_tarski(sK5(sK2,sK3,sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))),sK6(sK2,sK3,sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)))) = sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_32])])).

fof(f97,plain,
    ( spl10_10
  <=> r2_hidden(sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f126,plain,
    ( k4_tarski(sK5(sK2,sK3,sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))),sK6(sK2,sK3,sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)))) = sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))
    | ~ spl10_10 ),
    inference(resolution,[],[f38,f98])).

fof(f98,plain,
    ( r2_hidden(sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK2,sK3))
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f97])).

fof(f239,plain,
    ( ~ spl10_31
    | ~ spl10_10 ),
    inference(avatar_split_clause,[],[f205,f97,f237])).

fof(f205,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl10_10 ),
    inference(resolution,[],[f64,f98])).

fof(f232,plain,
    ( ~ spl10_29
    | ~ spl10_6 ),
    inference(avatar_split_clause,[],[f223,f76,f230])).

fof(f230,plain,
    ( spl10_29
  <=> ~ r2_hidden(k2_zfmisc_1(sK0,sK1),sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_29])])).

fof(f223,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK0,sK1),sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))
    | ~ spl10_6 ),
    inference(resolution,[],[f77,f35])).

fof(f219,plain,
    ( ~ spl10_27
    | ~ spl10_10 ),
    inference(avatar_split_clause,[],[f191,f97,f217])).

fof(f191,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ spl10_10 ),
    inference(resolution,[],[f52,f98])).

fof(f212,plain,
    ( spl10_24
    | ~ spl10_8 ),
    inference(avatar_split_clause,[],[f125,f82,f210])).

fof(f125,plain,
    ( k4_tarski(sK5(sK2,sK3,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),sK6(sK2,sK3,sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))) = sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | ~ spl10_8 ),
    inference(resolution,[],[f38,f83])).

fof(f177,plain,
    ( ~ spl10_19
    | spl10_20
    | spl10_22 ),
    inference(avatar_split_clause,[],[f162,f175,f172,f169])).

fof(f169,plain,
    ( spl10_19
  <=> ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).

fof(f162,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,sK2)
      | ~ r2_hidden(X5,sK3)
      | ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ) ),
    inference(resolution,[],[f116,f34])).

fof(f157,plain,
    ( ~ spl10_17
    | ~ spl10_10 ),
    inference(avatar_split_clause,[],[f113,f97,f155])).

fof(f155,plain,
    ( spl10_17
  <=> ~ r2_hidden(k2_zfmisc_1(sK2,sK3),sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).

fof(f113,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK2,sK3),sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)))
    | ~ spl10_10 ),
    inference(resolution,[],[f98,f35])).

fof(f139,plain,
    ( ~ spl10_15
    | ~ spl10_8 ),
    inference(avatar_split_clause,[],[f94,f82,f137])).

fof(f137,plain,
    ( spl10_15
  <=> ~ r2_hidden(k2_zfmisc_1(sK2,sK3),sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).

fof(f94,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK2,sK3),sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))
    | ~ spl10_8 ),
    inference(resolution,[],[f83,f35])).

fof(f112,plain,
    ( spl10_1
    | spl10_11
    | spl10_13 ),
    inference(avatar_contradiction_clause,[],[f111])).

fof(f111,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_11
    | ~ spl10_13 ),
    inference(subsumption_resolution,[],[f110,f46])).

fof(f46,plain,
    ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(sK2,sK3)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl10_1
  <=> k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f110,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3)
    | ~ spl10_11
    | ~ spl10_13 ),
    inference(subsumption_resolution,[],[f109,f107])).

fof(f107,plain,
    ( ~ r2_hidden(sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ spl10_13 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl10_13
  <=> ~ r2_hidden(sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f109,plain,
    ( r2_hidden(sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3)
    | ~ spl10_11 ),
    inference(resolution,[],[f101,f31])).

fof(f101,plain,
    ( ~ r2_hidden(sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK2,sK3))
    | ~ spl10_11 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl10_11
  <=> ~ r2_hidden(sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f108,plain,
    ( ~ spl10_11
    | ~ spl10_13
    | spl10_1 ),
    inference(avatar_split_clause,[],[f71,f45,f106,f100])).

fof(f71,plain,
    ( ~ r2_hidden(sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ r2_hidden(sK9(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK2,sK3))
    | ~ spl10_1 ),
    inference(extensionality_resolution,[],[f32,f46])).

fof(f92,plain,
    ( spl10_1
    | spl10_7
    | spl10_9 ),
    inference(avatar_contradiction_clause,[],[f91])).

fof(f91,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_7
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f90,f46])).

fof(f90,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3)
    | ~ spl10_7
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f89,f80])).

fof(f89,plain,
    ( r2_hidden(sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK0,sK1))
    | k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3)
    | ~ spl10_9 ),
    inference(resolution,[],[f86,f31])).

fof(f87,plain,
    ( ~ spl10_7
    | ~ spl10_9
    | spl10_1 ),
    inference(avatar_split_clause,[],[f70,f45,f85,f79])).

fof(f70,plain,
    ( ~ r2_hidden(sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK2,sK3))
    | ~ r2_hidden(sK9(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK0,sK1))
    | ~ spl10_1 ),
    inference(extensionality_resolution,[],[f32,f46])).

fof(f62,plain,
    ( spl10_2
    | ~ spl10_5 ),
    inference(avatar_split_clause,[],[f49,f60,f54])).

fof(f60,plain,
    ( spl10_5
  <=> ~ v1_xboole_0(k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_zfmisc_1(sK2,sK3))
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1)) ) ),
    inference(resolution,[],[f34,f20])).

fof(f47,plain,(
    ~ spl10_1 ),
    inference(avatar_split_clause,[],[f21,f45])).

fof(f21,plain,(
    k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
