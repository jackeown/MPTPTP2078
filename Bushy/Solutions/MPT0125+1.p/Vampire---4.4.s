%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : enumset1__t41_enumset1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:35:59 EDT 2019

% Result     : Theorem 0.73s
% Output     : Refutation 0.73s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 306 expanded)
%              Number of leaves         :   28 ( 111 expanded)
%              Depth                    :    7
%              Number of atoms          :  380 ( 753 expanded)
%              Number of equality atoms :   60 ( 174 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f349,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f104,f111,f126,f133,f150,f163,f194,f209,f216,f221,f226,f234,f237,f241,f260,f267,f281,f286,f299,f300,f305,f319,f322,f327,f331,f345])).

fof(f345,plain,
    ( spl6_9
    | ~ spl6_14 ),
    inference(avatar_contradiction_clause,[],[f344])).

fof(f344,plain,
    ( $false
    | ~ spl6_9
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f333,f45])).

fof(f45,plain,(
    ! [X3,X1] : r2_hidden(X3,k2_tarski(X3,X1)) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,X2)
      | k2_tarski(X3,X1) != X2 ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X3
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t41_enumset1.p',d2_tarski)).

fof(f333,plain,
    ( ~ r2_hidden(sK0,k2_tarski(sK0,sK1))
    | ~ spl6_9
    | ~ spl6_14 ),
    inference(backward_demodulation,[],[f202,f125])).

fof(f125,plain,
    ( ~ r2_hidden(sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl6_9
  <=> ~ r2_hidden(sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f202,plain,
    ( sK0 = sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1))
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f201])).

fof(f201,plain,
    ( spl6_14
  <=> sK0 = sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f331,plain,
    ( ~ spl6_12
    | spl6_17 ),
    inference(avatar_contradiction_clause,[],[f330])).

fof(f330,plain,
    ( $false
    | ~ spl6_12
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f329,f205])).

fof(f205,plain,
    ( sK1 != sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1))
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f204])).

fof(f204,plain,
    ( spl6_17
  <=> sK1 != sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f329,plain,
    ( sK1 = sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1))
    | ~ spl6_12 ),
    inference(resolution,[],[f159,f47])).

fof(f47,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t41_enumset1.p',d1_tarski)).

fof(f159,plain,
    ( r2_hidden(sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1)),k1_tarski(sK1))
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl6_12
  <=> r2_hidden(sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1)),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f327,plain,
    ( spl6_17
    | spl6_31
    | spl6_33 ),
    inference(avatar_contradiction_clause,[],[f326])).

fof(f326,plain,
    ( $false
    | ~ spl6_17
    | ~ spl6_31
    | ~ spl6_33 ),
    inference(subsumption_resolution,[],[f325,f205])).

fof(f325,plain,
    ( sK1 = sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1))
    | ~ spl6_31
    | ~ spl6_33 ),
    inference(subsumption_resolution,[],[f324,f318])).

fof(f318,plain,
    ( ~ r2_hidden(sK5(sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1)),sK1),sK1)
    | ~ spl6_33 ),
    inference(avatar_component_clause,[],[f317])).

fof(f317,plain,
    ( spl6_33
  <=> ~ r2_hidden(sK5(sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1)),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f324,plain,
    ( r2_hidden(sK5(sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1)),sK1),sK1)
    | sK1 = sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1))
    | ~ spl6_31 ),
    inference(resolution,[],[f312,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X1)
      | r2_hidden(sK5(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t41_enumset1.p',t2_tarski)).

fof(f312,plain,
    ( ~ r2_hidden(sK5(sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1)),sK1),sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1)))
    | ~ spl6_31 ),
    inference(avatar_component_clause,[],[f311])).

fof(f311,plain,
    ( spl6_31
  <=> ~ r2_hidden(sK5(sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1)),sK1),sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f322,plain,
    ( ~ spl6_10
    | spl6_15 ),
    inference(avatar_contradiction_clause,[],[f321])).

fof(f321,plain,
    ( $false
    | ~ spl6_10
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f320,f199])).

fof(f199,plain,
    ( sK0 != sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1))
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f198])).

fof(f198,plain,
    ( spl6_15
  <=> sK0 != sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f320,plain,
    ( sK0 = sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1))
    | ~ spl6_10 ),
    inference(resolution,[],[f146,f47])).

fof(f146,plain,
    ( r2_hidden(sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1)),k1_tarski(sK0))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl6_10
  <=> r2_hidden(sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1)),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f319,plain,
    ( ~ spl6_31
    | ~ spl6_33
    | spl6_17 ),
    inference(avatar_split_clause,[],[f263,f204,f317,f311])).

fof(f263,plain,
    ( ~ r2_hidden(sK5(sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1)),sK1),sK1)
    | ~ r2_hidden(sK5(sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1)),sK1),sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1)))
    | ~ spl6_17 ),
    inference(extensionality_resolution,[],[f35,f205])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | ~ r2_hidden(sK5(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f305,plain,
    ( spl6_17
    | spl6_27
    | spl6_29 ),
    inference(avatar_contradiction_clause,[],[f304])).

fof(f304,plain,
    ( $false
    | ~ spl6_17
    | ~ spl6_27
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f303,f205])).

fof(f303,plain,
    ( sK1 = sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1))
    | ~ spl6_27
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f302,f292])).

fof(f292,plain,
    ( ~ r2_hidden(sK5(sK1,sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1))),sK1)
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f291])).

fof(f291,plain,
    ( spl6_27
  <=> ~ r2_hidden(sK5(sK1,sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f302,plain,
    ( r2_hidden(sK5(sK1,sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1))),sK1)
    | sK1 = sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1))
    | ~ spl6_29 ),
    inference(resolution,[],[f298,f34])).

fof(f298,plain,
    ( ~ r2_hidden(sK5(sK1,sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1))),sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1)))
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f297])).

fof(f297,plain,
    ( spl6_29
  <=> ~ r2_hidden(sK5(sK1,sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1))),sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f300,plain,
    ( spl6_10
    | ~ spl6_6
    | spl6_13 ),
    inference(avatar_split_clause,[],[f214,f161,f115,f145])).

fof(f115,plain,
    ( spl6_6
  <=> r2_hidden(sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1)),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f161,plain,
    ( spl6_13
  <=> ~ r2_hidden(sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1)),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f214,plain,
    ( r2_hidden(sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1)),k1_tarski(sK0))
    | ~ spl6_6
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f213,f162])).

fof(f162,plain,
    ( ~ r2_hidden(sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1)),k1_tarski(sK1))
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f161])).

fof(f213,plain,
    ( r2_hidden(sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1)),k1_tarski(sK1))
    | r2_hidden(sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1)),k1_tarski(sK0))
    | ~ spl6_6 ),
    inference(resolution,[],[f116,f41])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_xboole_0(X0,X1))
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t41_enumset1.p',d3_xboole_0)).

fof(f116,plain,
    ( r2_hidden(sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1)),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f115])).

fof(f299,plain,
    ( ~ spl6_27
    | ~ spl6_29
    | spl6_17 ),
    inference(avatar_split_clause,[],[f262,f204,f297,f291])).

fof(f262,plain,
    ( ~ r2_hidden(sK5(sK1,sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1))),sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1)))
    | ~ r2_hidden(sK5(sK1,sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1))),sK1)
    | ~ spl6_17 ),
    inference(extensionality_resolution,[],[f35,f205])).

fof(f286,plain,
    ( spl6_15
    | spl6_23
    | spl6_25 ),
    inference(avatar_contradiction_clause,[],[f285])).

fof(f285,plain,
    ( $false
    | ~ spl6_15
    | ~ spl6_23
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f284,f199])).

fof(f284,plain,
    ( sK0 = sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1))
    | ~ spl6_23
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f283,f280])).

fof(f280,plain,
    ( ~ r2_hidden(sK5(sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1)),sK0),sK0)
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f279])).

fof(f279,plain,
    ( spl6_25
  <=> ~ r2_hidden(sK5(sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1)),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f283,plain,
    ( r2_hidden(sK5(sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1)),sK0),sK0)
    | sK0 = sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1))
    | ~ spl6_23 ),
    inference(resolution,[],[f274,f34])).

fof(f274,plain,
    ( ~ r2_hidden(sK5(sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1)),sK0),sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1)))
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f273])).

fof(f273,plain,
    ( spl6_23
  <=> ~ r2_hidden(sK5(sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1)),sK0),sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f281,plain,
    ( ~ spl6_23
    | ~ spl6_25
    | spl6_15 ),
    inference(avatar_split_clause,[],[f246,f198,f279,f273])).

fof(f246,plain,
    ( ~ r2_hidden(sK5(sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1)),sK0),sK0)
    | ~ r2_hidden(sK5(sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1)),sK0),sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1)))
    | ~ spl6_15 ),
    inference(extensionality_resolution,[],[f35,f199])).

fof(f267,plain,
    ( spl6_15
    | spl6_19
    | spl6_21 ),
    inference(avatar_contradiction_clause,[],[f266])).

fof(f266,plain,
    ( $false
    | ~ spl6_15
    | ~ spl6_19
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f265,f199])).

fof(f265,plain,
    ( sK0 = sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1))
    | ~ spl6_19
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f264,f253])).

fof(f253,plain,
    ( ~ r2_hidden(sK5(sK0,sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1))),sK0)
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f252])).

fof(f252,plain,
    ( spl6_19
  <=> ~ r2_hidden(sK5(sK0,sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f264,plain,
    ( r2_hidden(sK5(sK0,sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1))),sK0)
    | sK0 = sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1))
    | ~ spl6_21 ),
    inference(resolution,[],[f259,f34])).

fof(f259,plain,
    ( ~ r2_hidden(sK5(sK0,sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1))),sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1)))
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f258])).

fof(f258,plain,
    ( spl6_21
  <=> ~ r2_hidden(sK5(sK0,sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1))),sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f260,plain,
    ( ~ spl6_19
    | ~ spl6_21
    | spl6_15 ),
    inference(avatar_split_clause,[],[f245,f198,f258,f252])).

fof(f245,plain,
    ( ~ r2_hidden(sK5(sK0,sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1))),sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1)))
    | ~ r2_hidden(sK5(sK0,sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1))),sK0)
    | ~ spl6_15 ),
    inference(extensionality_resolution,[],[f35,f199])).

fof(f241,plain,
    ( spl6_9
    | ~ spl6_16 ),
    inference(avatar_contradiction_clause,[],[f240])).

fof(f240,plain,
    ( $false
    | ~ spl6_9
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f239,f43])).

fof(f43,plain,(
    ! [X0,X3] : r2_hidden(X3,k2_tarski(X0,X3)) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(X3,X2)
      | k2_tarski(X0,X3) != X2 ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 != X3
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f239,plain,
    ( ~ r2_hidden(sK1,k2_tarski(sK0,sK1))
    | ~ spl6_9
    | ~ spl6_16 ),
    inference(forward_demodulation,[],[f125,f208])).

fof(f208,plain,
    ( sK1 = sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1))
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f207])).

fof(f207,plain,
    ( spl6_16
  <=> sK1 = sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f237,plain,
    ( spl6_13
    | ~ spl6_16 ),
    inference(avatar_contradiction_clause,[],[f236])).

fof(f236,plain,
    ( $false
    | ~ spl6_13
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f235,f49])).

fof(f49,plain,(
    ! [X2] : r2_hidden(X2,k1_tarski(X2)) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k1_tarski(X2) != X1 ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f235,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK1))
    | ~ spl6_13
    | ~ spl6_16 ),
    inference(forward_demodulation,[],[f162,f208])).

fof(f234,plain,
    ( spl6_7
    | ~ spl6_16 ),
    inference(avatar_contradiction_clause,[],[f233])).

fof(f233,plain,
    ( $false
    | ~ spl6_7
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f229,f49])).

fof(f229,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK1))
    | ~ spl6_7
    | ~ spl6_16 ),
    inference(backward_demodulation,[],[f208,f130])).

fof(f130,plain,
    ( ~ r2_hidden(sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1)),k1_tarski(sK1))
    | ~ spl6_7 ),
    inference(resolution,[],[f119,f39])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f119,plain,
    ( ~ r2_hidden(sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1)),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl6_7
  <=> ~ r2_hidden(sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1)),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f226,plain,
    ( spl6_7
    | ~ spl6_14 ),
    inference(avatar_contradiction_clause,[],[f225])).

fof(f225,plain,
    ( $false
    | ~ spl6_7
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f224,f49])).

fof(f224,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK0))
    | ~ spl6_7
    | ~ spl6_14 ),
    inference(forward_demodulation,[],[f129,f202])).

fof(f129,plain,
    ( ~ r2_hidden(sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1)),k1_tarski(sK0))
    | ~ spl6_7 ),
    inference(resolution,[],[f119,f40])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f221,plain,
    ( spl6_11
    | ~ spl6_14 ),
    inference(avatar_contradiction_clause,[],[f220])).

fof(f220,plain,
    ( $false
    | ~ spl6_11
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f217,f49])).

fof(f217,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK0))
    | ~ spl6_11
    | ~ spl6_14 ),
    inference(backward_demodulation,[],[f202,f149])).

fof(f149,plain,
    ( ~ r2_hidden(sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1)),k1_tarski(sK0))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl6_11
  <=> ~ r2_hidden(sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1)),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f216,plain,
    ( ~ spl6_6
    | spl6_11
    | spl6_13 ),
    inference(avatar_contradiction_clause,[],[f215])).

fof(f215,plain,
    ( $false
    | ~ spl6_6
    | ~ spl6_11
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f214,f149])).

fof(f209,plain,
    ( spl6_14
    | spl6_16
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f196,f121,f207,f201])).

fof(f121,plain,
    ( spl6_8
  <=> r2_hidden(sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f196,plain,
    ( sK1 = sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1))
    | sK0 = sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1))
    | ~ spl6_8 ),
    inference(resolution,[],[f122,f46])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_tarski(X0,X1))
      | X1 = X3
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f122,plain,
    ( r2_hidden(sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f121])).

fof(f194,plain,
    ( spl6_8
    | spl6_1
    | spl6_7 ),
    inference(avatar_split_clause,[],[f134,f118,f54,f121])).

fof(f54,plain,
    ( spl6_1
  <=> k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f134,plain,
    ( r2_hidden(sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1))
    | ~ spl6_1
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f128,f55])).

fof(f55,plain,
    ( k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f128,plain,
    ( r2_hidden(sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1))
    | k2_tarski(sK0,sK1) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | ~ spl6_7 ),
    inference(resolution,[],[f119,f34])).

fof(f163,plain,
    ( ~ spl6_13
    | spl6_7 ),
    inference(avatar_split_clause,[],[f130,f118,f161])).

fof(f150,plain,
    ( ~ spl6_11
    | spl6_7 ),
    inference(avatar_split_clause,[],[f129,f118,f148])).

fof(f133,plain,
    ( spl6_1
    | spl6_7
    | spl6_9 ),
    inference(avatar_contradiction_clause,[],[f132])).

fof(f132,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f131,f55])).

fof(f131,plain,
    ( k2_tarski(sK0,sK1) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f128,f125])).

fof(f126,plain,
    ( ~ spl6_7
    | ~ spl6_9
    | spl6_1 ),
    inference(avatar_split_clause,[],[f86,f54,f124,f118])).

fof(f86,plain,
    ( ~ r2_hidden(sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1))
    | ~ r2_hidden(sK5(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_tarski(sK0,sK1)),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))
    | ~ spl6_1 ),
    inference(extensionality_resolution,[],[f35,f55])).

fof(f111,plain,
    ( spl6_1
    | spl6_3
    | spl6_5 ),
    inference(avatar_contradiction_clause,[],[f110])).

fof(f110,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f109,f55])).

fof(f109,plain,
    ( k2_tarski(sK0,sK1) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f106,f97])).

fof(f97,plain,
    ( ~ r2_hidden(sK5(k2_tarski(sK0,sK1),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k2_tarski(sK0,sK1))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl6_3
  <=> ~ r2_hidden(sK5(k2_tarski(sK0,sK1),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f106,plain,
    ( r2_hidden(sK5(k2_tarski(sK0,sK1),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k2_tarski(sK0,sK1))
    | k2_tarski(sK0,sK1) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | ~ spl6_5 ),
    inference(resolution,[],[f103,f34])).

fof(f103,plain,
    ( ~ r2_hidden(sK5(k2_tarski(sK0,sK1),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl6_5
  <=> ~ r2_hidden(sK5(k2_tarski(sK0,sK1),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f104,plain,
    ( ~ spl6_3
    | ~ spl6_5
    | spl6_1 ),
    inference(avatar_split_clause,[],[f85,f54,f102,f96])).

fof(f85,plain,
    ( ~ r2_hidden(sK5(k2_tarski(sK0,sK1),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))
    | ~ r2_hidden(sK5(k2_tarski(sK0,sK1),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k2_tarski(sK0,sK1))
    | ~ spl6_1 ),
    inference(extensionality_resolution,[],[f35,f55])).

fof(f56,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f17,f54])).

fof(f17,plain,(
    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t41_enumset1.p',t41_enumset1)).
%------------------------------------------------------------------------------
