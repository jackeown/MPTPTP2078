%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:09 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 250 expanded)
%              Number of leaves         :   26 (  87 expanded)
%              Depth                    :   15
%              Number of atoms          :  423 (1043 expanded)
%              Number of equality atoms :  166 ( 440 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f300,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f71,f96,f101,f105,f123,f136,f201,f244,f248,f268,f276,f297])).

fof(f297,plain,
    ( ~ spl7_8
    | ~ spl7_12 ),
    inference(avatar_contradiction_clause,[],[f293])).

fof(f293,plain,
    ( $false
    | ~ spl7_8
    | ~ spl7_12 ),
    inference(resolution,[],[f286,f173])).

fof(f173,plain,
    ( r2_hidden(sK4(sK0,k1_xboole_0),k1_xboole_0)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl7_12
  <=> r2_hidden(sK4(sK0,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f286,plain,
    ( ! [X2] : ~ r2_hidden(X2,k1_xboole_0)
    | ~ spl7_8 ),
    inference(resolution,[],[f271,f40])).

fof(f40,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f271,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,sK0)
        | ~ r2_hidden(X0,X1) )
    | ~ spl7_8 ),
    inference(resolution,[],[f135,f53])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f29,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

% (3801)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f135,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK0)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl7_8
  <=> ! [X1] : ~ r2_hidden(X1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f276,plain,
    ( ~ spl7_8
    | ~ spl7_11 ),
    inference(avatar_contradiction_clause,[],[f272])).

fof(f272,plain,
    ( $false
    | ~ spl7_8
    | ~ spl7_11 ),
    inference(resolution,[],[f135,f169])).

fof(f169,plain,
    ( r2_hidden(sK4(sK0,k1_xboole_0),sK0)
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl7_11
  <=> r2_hidden(sK4(sK0,k1_xboole_0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f268,plain,
    ( ~ spl7_5
    | ~ spl7_4
    | ~ spl7_17
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f73,f68,f241,f93,f98])).

fof(f98,plain,
    ( spl7_5
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f93,plain,
    ( spl7_4
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f241,plain,
    ( spl7_17
  <=> r1_tarski(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f68,plain,
    ( spl7_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f73,plain,
    ( k1_xboole_0 != sK1
    | ~ r1_tarski(k1_xboole_0,sK0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f72,f38])).

fof(f38,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f72,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | k1_relat_1(k1_xboole_0) != sK1
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f37,f39])).

fof(f39,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f37,plain,(
    ! [X2] :
      ( ~ r1_tarski(k2_relat_1(X2),sK0)
      | k1_relat_1(X2) != sK1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k2_relat_1(X2),sK0)
        | k1_relat_1(X2) != sK1
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    & ( k1_xboole_0 = sK1
      | k1_xboole_0 != sK0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f19])).

fof(f19,plain,
    ( ? [X0,X1] :
        ( ! [X2] :
            ( ~ r1_tarski(k2_relat_1(X2),X0)
            | k1_relat_1(X2) != X1
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) )
        & ( k1_xboole_0 = X1
          | k1_xboole_0 != X0 ) )
   => ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),sK0)
          | k1_relat_1(X2) != sK1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = sK1
        | k1_xboole_0 != sK0 ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ~ ( r1_tarski(k2_relat_1(X2),X0)
                  & k1_relat_1(X2) = X1 ) )
          & ~ ( k1_xboole_0 != X1
              & k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

fof(f248,plain,(
    spl7_17 ),
    inference(avatar_contradiction_clause,[],[f247])).

fof(f247,plain,
    ( $false
    | spl7_17 ),
    inference(resolution,[],[f243,f40])).

fof(f243,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | spl7_17 ),
    inference(avatar_component_clause,[],[f241])).

fof(f244,plain,
    ( ~ spl7_5
    | ~ spl7_4
    | ~ spl7_17
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f239,f121,f241,f93,f98])).

fof(f121,plain,
    ( spl7_7
  <=> ! [X0] :
        ( sK1 != X0
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f239,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl7_7 ),
    inference(trivial_inequality_removal,[],[f238])).

fof(f238,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,sK0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl7_7 ),
    inference(forward_demodulation,[],[f73,f213])).

fof(f213,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_7 ),
    inference(equality_resolution,[],[f122])).

fof(f122,plain,
    ( ! [X0] :
        ( sK1 != X0
        | k1_xboole_0 = X0 )
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f121])).

fof(f201,plain,
    ( spl7_11
    | spl7_1
    | spl7_12 ),
    inference(avatar_split_clause,[],[f199,f172,f64,f168])).

fof(f64,plain,
    ( spl7_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f199,plain,
    ( k1_xboole_0 = sK0
    | r2_hidden(sK4(sK0,k1_xboole_0),sK0)
    | spl7_12 ),
    inference(resolution,[],[f174,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | X0 = X1
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK4(X0,X1),X1)
          | ~ r2_hidden(sK4(X0,X1),X0) )
        & ( r2_hidden(sK4(X0,X1),X1)
          | r2_hidden(sK4(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK4(X0,X1),X1)
          | ~ r2_hidden(sK4(X0,X1),X0) )
        & ( r2_hidden(sK4(X0,X1),X1)
          | r2_hidden(sK4(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(f174,plain,
    ( ~ r2_hidden(sK4(sK0,k1_xboole_0),k1_xboole_0)
    | spl7_12 ),
    inference(avatar_component_clause,[],[f172])).

fof(f136,plain,
    ( spl7_8
    | spl7_7
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f132,f118,f121,f134])).

fof(f118,plain,
    ( spl7_6
  <=> ! [X1] : sK5(k1_tarski(X1),sK0) = X1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f132,plain,
    ( ! [X0,X1] :
        ( sK1 != X0
        | ~ r2_hidden(X1,sK0)
        | k1_xboole_0 = X0 )
    | ~ spl7_6 ),
    inference(duplicate_literal_removal,[],[f131])).

fof(f131,plain,
    ( ! [X0,X1] :
        ( sK1 != X0
        | ~ r2_hidden(X1,sK0)
        | k1_xboole_0 = X0
        | k1_xboole_0 = X0 )
    | ~ spl7_6 ),
    inference(superposition,[],[f130,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_relat_1(sK2(X0,X1)) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tarski(X1) = k2_relat_1(sK2(X0,X1))
          & k1_relat_1(sK2(X0,X1)) = X0
          & v1_funct_1(sK2(X0,X1))
          & v1_relat_1(sK2(X0,X1)) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( k1_tarski(X1) = k2_relat_1(sK2(X0,X1))
        & k1_relat_1(sK2(X0,X1)) = X0
        & v1_funct_1(sK2(X0,X1))
        & v1_relat_1(sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

fof(f130,plain,
    ( ! [X0,X1] :
        ( sK1 != k1_relat_1(sK2(X1,X0))
        | ~ r2_hidden(X0,sK0)
        | k1_xboole_0 = X1 )
    | ~ spl7_6 ),
    inference(duplicate_literal_removal,[],[f129])).

fof(f129,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK0)
        | sK1 != k1_relat_1(sK2(X1,X0))
        | k1_xboole_0 = X1
        | k1_xboole_0 = X1 )
    | ~ spl7_6 ),
    inference(resolution,[],[f128,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f128,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(sK2(X0,X1))
        | ~ r2_hidden(X1,sK0)
        | sK1 != k1_relat_1(sK2(X0,X1))
        | k1_xboole_0 = X0 )
    | ~ spl7_6 ),
    inference(duplicate_literal_removal,[],[f127])).

fof(f127,plain,
    ( ! [X0,X1] :
        ( sK1 != k1_relat_1(sK2(X0,X1))
        | ~ r2_hidden(X1,sK0)
        | ~ v1_relat_1(sK2(X0,X1))
        | k1_xboole_0 = X0
        | k1_xboole_0 = X0 )
    | ~ spl7_6 ),
    inference(resolution,[],[f126,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f126,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(sK2(X1,X0))
        | sK1 != k1_relat_1(sK2(X1,X0))
        | ~ r2_hidden(X0,sK0)
        | ~ v1_relat_1(sK2(X1,X0))
        | k1_xboole_0 = X1 )
    | ~ spl7_6 ),
    inference(resolution,[],[f124,f103])).

fof(f103,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k1_tarski(X3),sK0)
      | sK1 != k1_relat_1(sK2(X2,X3))
      | ~ v1_funct_1(sK2(X2,X3))
      | ~ v1_relat_1(sK2(X2,X3))
      | k1_xboole_0 = X2 ) ),
    inference(superposition,[],[f37,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k2_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f124,plain,
    ( ! [X0] :
        ( r1_tarski(k1_tarski(X0),sK0)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl7_6 ),
    inference(superposition,[],[f55,f119])).

fof(f119,plain,
    ( ! [X1] : sK5(k1_tarski(X1),sK0) = X1
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f118])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f123,plain,
    ( spl7_6
    | spl7_7 ),
    inference(avatar_split_clause,[],[f116,f121,f118])).

fof(f116,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | sK5(k1_tarski(X1),sK0) = X1
      | k1_xboole_0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | sK5(k1_tarski(X1),sK0) = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f114,f45])).

fof(f114,plain,(
    ! [X0,X1] :
      ( sK1 != k1_relat_1(sK2(X1,X0))
      | sK5(k1_tarski(X0),sK0) = X0
      | k1_xboole_0 = X1 ) ),
    inference(duplicate_literal_removal,[],[f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( sK5(k1_tarski(X0),sK0) = X0
      | sK1 != k1_relat_1(sK2(X1,X0))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f110,f43])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK2(X0,X1))
      | sK5(k1_tarski(X1),sK0) = X1
      | sK1 != k1_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( sK1 != k1_relat_1(sK2(X0,X1))
      | sK5(k1_tarski(X1),sK0) = X1
      | ~ v1_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f108,f44])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(sK2(X1,X0))
      | sK1 != k1_relat_1(sK2(X1,X0))
      | sK5(k1_tarski(X0),sK0) = X0
      | ~ v1_relat_1(sK2(X1,X0))
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f75,f103])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | sK5(k1_tarski(X0),X1) = X0 ) ),
    inference(resolution,[],[f54,f62])).

fof(f62,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK6(X0,X1) != X0
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( sK6(X0,X1) = X0
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f33,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK6(X0,X1) != X0
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( sK6(X0,X1) = X0
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f105,plain,(
    ~ spl7_3 ),
    inference(avatar_contradiction_clause,[],[f104])).

fof(f104,plain,
    ( $false
    | ~ spl7_3 ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,
    ( ! [X4] : k1_xboole_0 != X4
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl7_3
  <=> ! [X4] : k1_xboole_0 != X4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f101,plain,
    ( spl7_3
    | spl7_5 ),
    inference(avatar_split_clause,[],[f88,f98,f90])).

fof(f88,plain,(
    ! [X5] :
      ( v1_relat_1(k1_xboole_0)
      | k1_xboole_0 != X5 ) ),
    inference(superposition,[],[f47,f83])).

fof(f83,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK3(X0)
      | k1_xboole_0 != X0 ) ),
    inference(superposition,[],[f78,f49])).

fof(f49,plain,(
    ! [X0] : k1_relat_1(sK3(X0)) = X0 ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(sK3(X0),X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK3(X0)) = X0
      & v1_funct_1(sK3(X0))
      & v1_relat_1(sK3(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f23])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_xboole_0 = k1_funct_1(X1,X2)
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( k1_xboole_0 = k1_funct_1(sK3(X0),X2)
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK3(X0)) = X0
        & v1_funct_1(sK3(X0))
        & v1_relat_1(sK3(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_xboole_0 = k1_funct_1(X1,X2) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

fof(f78,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(sK3(X0))
      | k1_xboole_0 = sK3(X0) ) ),
    inference(resolution,[],[f41,f47])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f47,plain,(
    ! [X0] : v1_relat_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f96,plain,
    ( spl7_3
    | spl7_4 ),
    inference(avatar_split_clause,[],[f87,f93,f90])).

fof(f87,plain,(
    ! [X4] :
      ( v1_funct_1(k1_xboole_0)
      | k1_xboole_0 != X4 ) ),
    inference(superposition,[],[f48,f83])).

fof(f48,plain,(
    ! [X0] : v1_funct_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f71,plain,
    ( ~ spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f36,f68,f64])).

fof(f36,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:19:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.49  % (3797)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.49  % (3805)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (3813)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.50  % (3805)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % (3818)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.51  % (3809)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f300,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f71,f96,f101,f105,f123,f136,f201,f244,f248,f268,f276,f297])).
% 0.20/0.51  fof(f297,plain,(
% 0.20/0.51    ~spl7_8 | ~spl7_12),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f293])).
% 0.20/0.51  fof(f293,plain,(
% 0.20/0.51    $false | (~spl7_8 | ~spl7_12)),
% 0.20/0.51    inference(resolution,[],[f286,f173])).
% 0.20/0.51  fof(f173,plain,(
% 0.20/0.51    r2_hidden(sK4(sK0,k1_xboole_0),k1_xboole_0) | ~spl7_12),
% 0.20/0.51    inference(avatar_component_clause,[],[f172])).
% 0.20/0.51  fof(f172,plain,(
% 0.20/0.51    spl7_12 <=> r2_hidden(sK4(sK0,k1_xboole_0),k1_xboole_0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.20/0.51  fof(f286,plain,(
% 0.20/0.51    ( ! [X2] : (~r2_hidden(X2,k1_xboole_0)) ) | ~spl7_8),
% 0.20/0.51    inference(resolution,[],[f271,f40])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.51  fof(f271,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_tarski(X1,sK0) | ~r2_hidden(X0,X1)) ) | ~spl7_8),
% 0.20/0.51    inference(resolution,[],[f135,f53])).
% 0.20/0.51  fof(f53,plain,(
% 0.20/0.51    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f31])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f29,f30])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  % (3801)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.51    inference(rectify,[],[f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.51    inference(nnf_transformation,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.51  fof(f135,plain,(
% 0.20/0.51    ( ! [X1] : (~r2_hidden(X1,sK0)) ) | ~spl7_8),
% 0.20/0.51    inference(avatar_component_clause,[],[f134])).
% 0.20/0.51  fof(f134,plain,(
% 0.20/0.51    spl7_8 <=> ! [X1] : ~r2_hidden(X1,sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.20/0.51  fof(f276,plain,(
% 0.20/0.51    ~spl7_8 | ~spl7_11),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f272])).
% 0.20/0.51  fof(f272,plain,(
% 0.20/0.51    $false | (~spl7_8 | ~spl7_11)),
% 0.20/0.51    inference(resolution,[],[f135,f169])).
% 0.20/0.51  fof(f169,plain,(
% 0.20/0.51    r2_hidden(sK4(sK0,k1_xboole_0),sK0) | ~spl7_11),
% 0.20/0.51    inference(avatar_component_clause,[],[f168])).
% 0.20/0.51  fof(f168,plain,(
% 0.20/0.51    spl7_11 <=> r2_hidden(sK4(sK0,k1_xboole_0),sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.20/0.51  fof(f268,plain,(
% 0.20/0.51    ~spl7_5 | ~spl7_4 | ~spl7_17 | ~spl7_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f73,f68,f241,f93,f98])).
% 0.20/0.51  fof(f98,plain,(
% 0.20/0.51    spl7_5 <=> v1_relat_1(k1_xboole_0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.20/0.51  fof(f93,plain,(
% 0.20/0.51    spl7_4 <=> v1_funct_1(k1_xboole_0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.20/0.51  fof(f241,plain,(
% 0.20/0.51    spl7_17 <=> r1_tarski(k1_xboole_0,sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 0.20/0.51  fof(f68,plain,(
% 0.20/0.51    spl7_2 <=> k1_xboole_0 = sK1),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.20/0.51  fof(f73,plain,(
% 0.20/0.51    k1_xboole_0 != sK1 | ~r1_tarski(k1_xboole_0,sK0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 0.20/0.51    inference(forward_demodulation,[],[f72,f38])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.51    inference(cnf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.51  fof(f72,plain,(
% 0.20/0.51    ~r1_tarski(k1_xboole_0,sK0) | k1_relat_1(k1_xboole_0) != sK1 | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 0.20/0.51    inference(superposition,[],[f37,f39])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.20/0.51    inference(cnf_transformation,[],[f5])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ( ! [X2] : (~r1_tarski(k2_relat_1(X2),sK0) | k1_relat_1(X2) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ! [X2] : (~r1_tarski(k2_relat_1(X2),sK0) | k1_relat_1(X2) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK0)),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0)) => (! [X2] : (~r1_tarski(k2_relat_1(X2),sK0) | k1_relat_1(X2) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK0))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 0.20/0.51    inference(flattening,[],[f11])).
% 0.20/0.51  fof(f11,plain,(
% 0.20/0.51    ? [X0,X1] : (! [X2] : ((~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,negated_conjecture,(
% 0.20/0.51    ~! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.20/0.51    inference(negated_conjecture,[],[f9])).
% 0.20/0.51  fof(f9,conjecture,(
% 0.20/0.51    ! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).
% 0.20/0.51  fof(f248,plain,(
% 0.20/0.51    spl7_17),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f247])).
% 0.20/0.51  fof(f247,plain,(
% 0.20/0.51    $false | spl7_17),
% 0.20/0.51    inference(resolution,[],[f243,f40])).
% 0.20/0.51  fof(f243,plain,(
% 0.20/0.51    ~r1_tarski(k1_xboole_0,sK0) | spl7_17),
% 0.20/0.51    inference(avatar_component_clause,[],[f241])).
% 0.20/0.51  fof(f244,plain,(
% 0.20/0.51    ~spl7_5 | ~spl7_4 | ~spl7_17 | ~spl7_7),
% 0.20/0.51    inference(avatar_split_clause,[],[f239,f121,f241,f93,f98])).
% 0.20/0.51  fof(f121,plain,(
% 0.20/0.51    spl7_7 <=> ! [X0] : (sK1 != X0 | k1_xboole_0 = X0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.20/0.51  fof(f239,plain,(
% 0.20/0.51    ~r1_tarski(k1_xboole_0,sK0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~spl7_7),
% 0.20/0.51    inference(trivial_inequality_removal,[],[f238])).
% 0.20/0.51  fof(f238,plain,(
% 0.20/0.51    k1_xboole_0 != k1_xboole_0 | ~r1_tarski(k1_xboole_0,sK0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~spl7_7),
% 0.20/0.51    inference(forward_demodulation,[],[f73,f213])).
% 0.20/0.51  fof(f213,plain,(
% 0.20/0.51    k1_xboole_0 = sK1 | ~spl7_7),
% 0.20/0.51    inference(equality_resolution,[],[f122])).
% 0.20/0.51  fof(f122,plain,(
% 0.20/0.51    ( ! [X0] : (sK1 != X0 | k1_xboole_0 = X0) ) | ~spl7_7),
% 0.20/0.51    inference(avatar_component_clause,[],[f121])).
% 0.20/0.51  fof(f201,plain,(
% 0.20/0.51    spl7_11 | spl7_1 | spl7_12),
% 0.20/0.51    inference(avatar_split_clause,[],[f199,f172,f64,f168])).
% 0.20/0.51  fof(f64,plain,(
% 0.20/0.51    spl7_1 <=> k1_xboole_0 = sK0),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.20/0.51  fof(f199,plain,(
% 0.20/0.51    k1_xboole_0 = sK0 | r2_hidden(sK4(sK0,k1_xboole_0),sK0) | spl7_12),
% 0.20/0.51    inference(resolution,[],[f174,f51])).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | X0 = X1 | r2_hidden(sK4(X0,X1),X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK4(X0,X1),X1) | ~r2_hidden(sK4(X0,X1),X0)) & (r2_hidden(sK4(X0,X1),X1) | r2_hidden(sK4(X0,X1),X0))))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK4(X0,X1),X1) | ~r2_hidden(sK4(X0,X1),X0)) & (r2_hidden(sK4(X0,X1),X1) | r2_hidden(sK4(X0,X1),X0))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 0.20/0.51    inference(nnf_transformation,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 0.20/0.51    inference(ennf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).
% 0.20/0.51  fof(f174,plain,(
% 0.20/0.51    ~r2_hidden(sK4(sK0,k1_xboole_0),k1_xboole_0) | spl7_12),
% 0.20/0.51    inference(avatar_component_clause,[],[f172])).
% 0.20/0.51  fof(f136,plain,(
% 0.20/0.51    spl7_8 | spl7_7 | ~spl7_6),
% 0.20/0.51    inference(avatar_split_clause,[],[f132,f118,f121,f134])).
% 0.20/0.51  fof(f118,plain,(
% 0.20/0.51    spl7_6 <=> ! [X1] : sK5(k1_tarski(X1),sK0) = X1),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.20/0.51  fof(f132,plain,(
% 0.20/0.51    ( ! [X0,X1] : (sK1 != X0 | ~r2_hidden(X1,sK0) | k1_xboole_0 = X0) ) | ~spl7_6),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f131])).
% 0.20/0.51  fof(f131,plain,(
% 0.20/0.51    ( ! [X0,X1] : (sK1 != X0 | ~r2_hidden(X1,sK0) | k1_xboole_0 = X0 | k1_xboole_0 = X0) ) | ~spl7_6),
% 0.20/0.51    inference(superposition,[],[f130,f45])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_relat_1(sK2(X0,X1)) = X0 | k1_xboole_0 = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (k1_tarski(X1) = k2_relat_1(sK2(X0,X1)) & k1_relat_1(sK2(X0,X1)) = X0 & v1_funct_1(sK2(X0,X1)) & v1_relat_1(sK2(X0,X1))) | k1_xboole_0 = X0)),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ! [X1,X0] : (? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (k1_tarski(X1) = k2_relat_1(sK2(X0,X1)) & k1_relat_1(sK2(X0,X1)) = X0 & v1_funct_1(sK2(X0,X1)) & v1_relat_1(sK2(X0,X1))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) | k1_xboole_0 = X0)),
% 0.20/0.51    inference(ennf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).
% 0.20/0.51  fof(f130,plain,(
% 0.20/0.51    ( ! [X0,X1] : (sK1 != k1_relat_1(sK2(X1,X0)) | ~r2_hidden(X0,sK0) | k1_xboole_0 = X1) ) | ~spl7_6),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f129])).
% 0.20/0.51  fof(f129,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | sK1 != k1_relat_1(sK2(X1,X0)) | k1_xboole_0 = X1 | k1_xboole_0 = X1) ) | ~spl7_6),
% 0.20/0.51    inference(resolution,[],[f128,f43])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f22])).
% 0.20/0.51  fof(f128,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v1_relat_1(sK2(X0,X1)) | ~r2_hidden(X1,sK0) | sK1 != k1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) ) | ~spl7_6),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f127])).
% 0.20/0.51  fof(f127,plain,(
% 0.20/0.51    ( ! [X0,X1] : (sK1 != k1_relat_1(sK2(X0,X1)) | ~r2_hidden(X1,sK0) | ~v1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0 | k1_xboole_0 = X0) ) | ~spl7_6),
% 0.20/0.51    inference(resolution,[],[f126,f44])).
% 0.20/0.51  fof(f44,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v1_funct_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f22])).
% 0.20/0.51  fof(f126,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v1_funct_1(sK2(X1,X0)) | sK1 != k1_relat_1(sK2(X1,X0)) | ~r2_hidden(X0,sK0) | ~v1_relat_1(sK2(X1,X0)) | k1_xboole_0 = X1) ) | ~spl7_6),
% 0.20/0.51    inference(resolution,[],[f124,f103])).
% 0.20/0.51  fof(f103,plain,(
% 0.20/0.51    ( ! [X2,X3] : (~r1_tarski(k1_tarski(X3),sK0) | sK1 != k1_relat_1(sK2(X2,X3)) | ~v1_funct_1(sK2(X2,X3)) | ~v1_relat_1(sK2(X2,X3)) | k1_xboole_0 = X2) )),
% 0.20/0.51    inference(superposition,[],[f37,f46])).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_tarski(X1) = k2_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f22])).
% 0.20/0.51  fof(f124,plain,(
% 0.20/0.51    ( ! [X0] : (r1_tarski(k1_tarski(X0),sK0) | ~r2_hidden(X0,sK0)) ) | ~spl7_6),
% 0.20/0.51    inference(superposition,[],[f55,f119])).
% 0.20/0.51  fof(f119,plain,(
% 0.20/0.51    ( ! [X1] : (sK5(k1_tarski(X1),sK0) = X1) ) | ~spl7_6),
% 0.20/0.51    inference(avatar_component_clause,[],[f118])).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f31])).
% 0.20/0.51  fof(f123,plain,(
% 0.20/0.51    spl7_6 | spl7_7),
% 0.20/0.51    inference(avatar_split_clause,[],[f116,f121,f118])).
% 0.20/0.51  fof(f116,plain,(
% 0.20/0.51    ( ! [X0,X1] : (sK1 != X0 | sK5(k1_tarski(X1),sK0) = X1 | k1_xboole_0 = X0) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f115])).
% 0.20/0.51  fof(f115,plain,(
% 0.20/0.51    ( ! [X0,X1] : (sK1 != X0 | sK5(k1_tarski(X1),sK0) = X1 | k1_xboole_0 = X0 | k1_xboole_0 = X0) )),
% 0.20/0.51    inference(superposition,[],[f114,f45])).
% 0.20/0.51  fof(f114,plain,(
% 0.20/0.51    ( ! [X0,X1] : (sK1 != k1_relat_1(sK2(X1,X0)) | sK5(k1_tarski(X0),sK0) = X0 | k1_xboole_0 = X1) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f113])).
% 0.20/0.51  fof(f113,plain,(
% 0.20/0.51    ( ! [X0,X1] : (sK5(k1_tarski(X0),sK0) = X0 | sK1 != k1_relat_1(sK2(X1,X0)) | k1_xboole_0 = X1 | k1_xboole_0 = X1) )),
% 0.20/0.51    inference(resolution,[],[f110,f43])).
% 0.20/0.51  fof(f110,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v1_relat_1(sK2(X0,X1)) | sK5(k1_tarski(X1),sK0) = X1 | sK1 != k1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f109])).
% 0.20/0.51  fof(f109,plain,(
% 0.20/0.51    ( ! [X0,X1] : (sK1 != k1_relat_1(sK2(X0,X1)) | sK5(k1_tarski(X1),sK0) = X1 | ~v1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0 | k1_xboole_0 = X0) )),
% 0.20/0.51    inference(resolution,[],[f108,f44])).
% 0.20/0.51  fof(f108,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v1_funct_1(sK2(X1,X0)) | sK1 != k1_relat_1(sK2(X1,X0)) | sK5(k1_tarski(X0),sK0) = X0 | ~v1_relat_1(sK2(X1,X0)) | k1_xboole_0 = X1) )),
% 0.20/0.51    inference(resolution,[],[f75,f103])).
% 0.20/0.51  fof(f75,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | sK5(k1_tarski(X0),X1) = X0) )),
% 0.20/0.51    inference(resolution,[],[f54,f62])).
% 0.20/0.51  fof(f62,plain,(
% 0.20/0.51    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 0.20/0.51    inference(equality_resolution,[],[f56])).
% 0.20/0.51  fof(f56,plain,(
% 0.20/0.51    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.20/0.51    inference(cnf_transformation,[],[f35])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK6(X0,X1) != X0 | ~r2_hidden(sK6(X0,X1),X1)) & (sK6(X0,X1) = X0 | r2_hidden(sK6(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f33,f34])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK6(X0,X1) != X0 | ~r2_hidden(sK6(X0,X1),X1)) & (sK6(X0,X1) = X0 | r2_hidden(sK6(X0,X1),X1))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.20/0.51    inference(rectify,[],[f32])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.20/0.51    inference(nnf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.20/0.51  fof(f54,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f31])).
% 0.20/0.51  fof(f105,plain,(
% 0.20/0.51    ~spl7_3),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f104])).
% 0.20/0.51  fof(f104,plain,(
% 0.20/0.51    $false | ~spl7_3),
% 0.20/0.51    inference(equality_resolution,[],[f91])).
% 0.20/0.51  fof(f91,plain,(
% 0.20/0.51    ( ! [X4] : (k1_xboole_0 != X4) ) | ~spl7_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f90])).
% 0.20/0.51  fof(f90,plain,(
% 0.20/0.51    spl7_3 <=> ! [X4] : k1_xboole_0 != X4),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.20/0.51  fof(f101,plain,(
% 0.20/0.51    spl7_3 | spl7_5),
% 0.20/0.51    inference(avatar_split_clause,[],[f88,f98,f90])).
% 0.20/0.51  fof(f88,plain,(
% 0.20/0.51    ( ! [X5] : (v1_relat_1(k1_xboole_0) | k1_xboole_0 != X5) )),
% 0.20/0.51    inference(superposition,[],[f47,f83])).
% 0.20/0.51  fof(f83,plain,(
% 0.20/0.51    ( ! [X0] : (k1_xboole_0 = sK3(X0) | k1_xboole_0 != X0) )),
% 0.20/0.51    inference(superposition,[],[f78,f49])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    ( ! [X0] : (k1_relat_1(sK3(X0)) = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ! [X0] : (! [X2] : (k1_xboole_0 = k1_funct_1(sK3(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK3(X0)) = X0 & v1_funct_1(sK3(X0)) & v1_relat_1(sK3(X0)))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ! [X0] : (? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : (k1_xboole_0 = k1_funct_1(sK3(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK3(X0)) = X0 & v1_funct_1(sK3(X0)) & v1_relat_1(sK3(X0))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ! [X0] : ? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_xboole_0 = k1_funct_1(X1,X2)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).
% 0.20/0.51  fof(f78,plain,(
% 0.20/0.51    ( ! [X0] : (k1_xboole_0 != k1_relat_1(sK3(X0)) | k1_xboole_0 = sK3(X0)) )),
% 0.20/0.51    inference(resolution,[],[f41,f47])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(flattening,[],[f13])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    ( ! [X0] : (v1_relat_1(sK3(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f24])).
% 0.20/0.51  fof(f96,plain,(
% 0.20/0.51    spl7_3 | spl7_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f87,f93,f90])).
% 0.20/0.51  fof(f87,plain,(
% 0.20/0.51    ( ! [X4] : (v1_funct_1(k1_xboole_0) | k1_xboole_0 != X4) )),
% 0.20/0.51    inference(superposition,[],[f48,f83])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    ( ! [X0] : (v1_funct_1(sK3(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f24])).
% 0.20/0.51  fof(f71,plain,(
% 0.20/0.51    ~spl7_1 | spl7_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f36,f68,f64])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    k1_xboole_0 = sK1 | k1_xboole_0 != sK0),
% 0.20/0.51    inference(cnf_transformation,[],[f20])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (3805)------------------------------
% 0.20/0.51  % (3805)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (3805)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (3805)Memory used [KB]: 6268
% 0.20/0.51  % (3805)Time elapsed: 0.091 s
% 0.20/0.51  % (3805)------------------------------
% 0.20/0.51  % (3805)------------------------------
% 0.20/0.51  % (3792)Success in time 0.154 s
%------------------------------------------------------------------------------
