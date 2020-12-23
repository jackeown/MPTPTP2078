%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 185 expanded)
%              Number of leaves         :   16 (  55 expanded)
%              Depth                    :   14
%              Number of atoms          :  291 ( 714 expanded)
%              Number of equality atoms :   16 (  33 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f979,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f803,f821,f975,f978])).

fof(f978,plain,
    ( spl8_3
    | spl8_4
    | ~ spl8_1 ),
    inference(avatar_split_clause,[],[f977,f57,f801,f798])).

fof(f798,plain,
    ( spl8_3
  <=> ! [X1] : ~ r2_hidden(X1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f801,plain,
    ( spl8_4
  <=> ! [X0] :
        ( r2_hidden(X0,sK4)
        | ~ r2_hidden(X0,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f57,plain,
    ( spl8_1
  <=> r1_tarski(k2_zfmisc_1(sK3,sK2),k2_zfmisc_1(sK4,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f977,plain,
    ( ! [X2,X3] :
        ( r2_hidden(X2,sK4)
        | ~ r2_hidden(X3,sK2)
        | ~ r2_hidden(X2,sK3) )
    | ~ spl8_1 ),
    inference(resolution,[],[f59,f177])).

fof(f177,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X2,X3),k2_zfmisc_1(X1,X4))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X5,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(resolution,[],[f105,f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f105,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X2),X3)
      | r2_hidden(X0,X1)
      | ~ r1_tarski(X3,k2_zfmisc_1(X1,X4)) ) ),
    inference(resolution,[],[f52,f40])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f20,f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f59,plain,
    ( r1_tarski(k2_zfmisc_1(sK3,sK2),k2_zfmisc_1(sK4,sK2))
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f975,plain,(
    ~ spl8_4 ),
    inference(avatar_contradiction_clause,[],[f974])).

fof(f974,plain,
    ( $false
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f973,f35])).

fof(f35,plain,(
    ~ r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ r1_tarski(sK3,sK4)
    & ( r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK4))
      | r1_tarski(k2_zfmisc_1(sK3,sK2),k2_zfmisc_1(sK4,sK2)) )
    & k1_xboole_0 != sK2 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f9,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X1,X2)
        & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
          | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
        & k1_xboole_0 != X0 )
   => ( ~ r1_tarski(sK3,sK4)
      & ( r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK4))
        | r1_tarski(k2_zfmisc_1(sK3,sK2),k2_zfmisc_1(sK4,sK2)) )
      & k1_xboole_0 != sK2 ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X1,X2)
      & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
        | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ r1_tarski(X1,X2)
          & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
            | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_tarski(X1,X2)
        & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
          | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(f973,plain,
    ( r1_tarski(sK3,sK4)
    | ~ spl8_4 ),
    inference(duplicate_literal_removal,[],[f971])).

fof(f971,plain,
    ( r1_tarski(sK3,sK4)
    | r1_tarski(sK3,sK4)
    | ~ spl8_4 ),
    inference(resolution,[],[f828,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f828,plain,
    ( ! [X19] :
        ( ~ r2_hidden(sK6(X19,sK4),sK3)
        | r1_tarski(X19,sK4) )
    | ~ spl8_4 ),
    inference(resolution,[],[f802,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f802,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK4)
        | ~ r2_hidden(X0,sK3) )
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f801])).

fof(f821,plain,(
    ~ spl8_3 ),
    inference(avatar_contradiction_clause,[],[f820])).

fof(f820,plain,
    ( $false
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f819,f33])).

fof(f33,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f16])).

fof(f819,plain,
    ( k1_xboole_0 = sK2
    | ~ spl8_3 ),
    inference(resolution,[],[f807,f453])).

fof(f453,plain,(
    ! [X20] :
      ( ~ r1_tarski(X20,k1_xboole_0)
      | k1_xboole_0 = X20 ) ),
    inference(resolution,[],[f385,f198])).

fof(f198,plain,(
    ! [X2,X3] :
      ( ~ sP1(X3,k1_xboole_0,X2)
      | k1_xboole_0 = X2 ) ),
    inference(resolution,[],[f192,f86])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP1(X0,X1,X3)
      | X2 = X3
      | ~ sP1(X0,X1,X2) ) ),
    inference(superposition,[],[f51,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ~ sP1(X0,X1,X2) )
      & ( sP1(X0,X1,X2)
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> sP1(X0,X1,X2) ) ),
    inference(definition_folding,[],[f2,f13,f12])).

fof(f12,plain,(
    ! [X1,X3,X0] :
      ( sP0(X1,X3,X0)
    <=> ( r2_hidden(X3,X1)
        & r2_hidden(X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP0(X1,X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f192,plain,(
    ! [X0] : sP1(X0,k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f186,f68])).

fof(f68,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(condensation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f39,f36])).

fof(f36,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f10,f17])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
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
    inference(rectify,[],[f3])).

fof(f3,axiom,(
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

fof(f186,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1,k1_xboole_0),X1)
      | sP1(X0,X1,k1_xboole_0) ) ),
    inference(resolution,[],[f139,f68])).

fof(f139,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X2),X2)
      | sP1(X0,X1,X2)
      | r2_hidden(sK7(X0,X1,X2),X1) ) ),
    inference(resolution,[],[f45,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ~ r2_hidden(X1,X0)
        | ~ r2_hidden(X1,X2) )
      & ( ( r2_hidden(X1,X0)
          & r2_hidden(X1,X2) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X1,X3,X0] :
      ( ( sP0(X1,X3,X0)
        | ~ r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP0(X1,X3,X0) ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X1,X3,X0] :
      ( ( sP0(X1,X3,X0)
        | ~ r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP0(X1,X3,X0) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,sK7(X0,X1,X2),X0)
      | sP1(X0,X1,X2)
      | r2_hidden(sK7(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ~ sP0(X1,sK7(X0,X1,X2),X0)
            | ~ r2_hidden(sK7(X0,X1,X2),X2) )
          & ( sP0(X1,sK7(X0,X1,X2),X0)
            | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X1,X4,X0) )
            & ( sP0(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f24,f25])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP0(X1,X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP0(X1,X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP0(X1,sK7(X0,X1,X2),X0)
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( sP0(X1,sK7(X0,X1,X2),X0)
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
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

fof(f385,plain,(
    ! [X10,X11] :
      ( sP1(X10,X11,X10)
      | ~ r1_tarski(X10,k1_xboole_0) ) ),
    inference(resolution,[],[f226,f75])).

fof(f75,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X3,X4)
      | ~ r1_tarski(X4,k1_xboole_0) ) ),
    inference(resolution,[],[f40,f68])).

fof(f226,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1,X0),X0)
      | sP1(X0,X1,X0) ) ),
    inference(factoring,[],[f140])).

fof(f140,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(sK7(X3,X4,X5),X5)
      | sP1(X3,X4,X5)
      | r2_hidden(sK7(X3,X4,X5),X3) ) ),
    inference(resolution,[],[f45,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f807,plain,
    ( ! [X4] : r1_tarski(sK2,X4)
    | ~ spl8_3 ),
    inference(resolution,[],[f799,f41])).

fof(f799,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK2)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f798])).

fof(f803,plain,
    ( spl8_3
    | spl8_4
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f791,f61,f801,f798])).

fof(f61,plain,
    ( spl8_2
  <=> r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f791,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK4)
        | ~ r2_hidden(X0,sK3)
        | ~ r2_hidden(X1,sK2) )
    | ~ spl8_2 ),
    inference(resolution,[],[f180,f63])).

fof(f63,plain,
    ( r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK4))
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f180,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X2,X3),k2_zfmisc_1(X4,X1))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X3)
      | ~ r2_hidden(X5,X2) ) ),
    inference(resolution,[],[f106,f54])).

fof(f106,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X0),X3)
      | r2_hidden(X0,X1)
      | ~ r1_tarski(X3,k2_zfmisc_1(X4,X1)) ) ),
    inference(resolution,[],[f53,f40])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f64,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f34,f61,f57])).

fof(f34,plain,
    ( r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK4))
    | r1_tarski(k2_zfmisc_1(sK3,sK2),k2_zfmisc_1(sK4,sK2)) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:28:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (18297)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.49  % (18315)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.52  % (18323)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  % (18298)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (18298)Refutation not found, incomplete strategy% (18298)------------------------------
% 0.21/0.53  % (18298)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (18298)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (18298)Memory used [KB]: 10618
% 0.21/0.53  % (18298)Time elapsed: 0.107 s
% 0.21/0.53  % (18298)------------------------------
% 0.21/0.53  % (18298)------------------------------
% 0.21/0.53  % (18299)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (18311)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (18301)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (18320)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (18313)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (18309)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (18300)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (18304)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (18324)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (18327)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (18325)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (18308)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (18302)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.55  % (18314)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (18318)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (18316)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (18318)Refutation not found, incomplete strategy% (18318)------------------------------
% 0.21/0.55  % (18318)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (18318)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (18318)Memory used [KB]: 1663
% 0.21/0.55  % (18318)Time elapsed: 0.104 s
% 0.21/0.55  % (18318)------------------------------
% 0.21/0.55  % (18318)------------------------------
% 0.21/0.55  % (18296)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.55  % (18314)Refutation not found, incomplete strategy% (18314)------------------------------
% 0.21/0.55  % (18314)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (18314)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (18314)Memory used [KB]: 10618
% 0.21/0.55  % (18314)Time elapsed: 0.142 s
% 0.21/0.55  % (18314)------------------------------
% 0.21/0.55  % (18314)------------------------------
% 0.21/0.55  % (18310)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.55  % (18307)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.56  % (18319)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.56  % (18312)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.56  % (18326)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.57  % (18317)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.57  % (18306)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.57  % (18322)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.58  % (18305)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.58  % (18319)Refutation not found, incomplete strategy% (18319)------------------------------
% 0.21/0.58  % (18319)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (18319)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (18319)Memory used [KB]: 10618
% 0.21/0.58  % (18319)Time elapsed: 0.171 s
% 0.21/0.58  % (18319)------------------------------
% 0.21/0.58  % (18319)------------------------------
% 0.21/0.58  % (18305)Refutation not found, incomplete strategy% (18305)------------------------------
% 0.21/0.58  % (18305)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (18305)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (18305)Memory used [KB]: 10618
% 0.21/0.58  % (18305)Time elapsed: 0.172 s
% 0.21/0.58  % (18305)------------------------------
% 0.21/0.58  % (18305)------------------------------
% 0.21/0.59  % (18317)Refutation not found, incomplete strategy% (18317)------------------------------
% 0.21/0.59  % (18317)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (18317)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.59  
% 0.21/0.59  % (18317)Memory used [KB]: 10746
% 0.21/0.59  % (18317)Time elapsed: 0.181 s
% 0.21/0.59  % (18317)------------------------------
% 0.21/0.59  % (18317)------------------------------
% 0.21/0.60  % (18325)Refutation found. Thanks to Tanya!
% 0.21/0.60  % SZS status Theorem for theBenchmark
% 1.93/0.62  % SZS output start Proof for theBenchmark
% 1.93/0.62  fof(f979,plain,(
% 1.93/0.62    $false),
% 1.93/0.62    inference(avatar_sat_refutation,[],[f64,f803,f821,f975,f978])).
% 1.93/0.62  fof(f978,plain,(
% 1.93/0.62    spl8_3 | spl8_4 | ~spl8_1),
% 1.93/0.62    inference(avatar_split_clause,[],[f977,f57,f801,f798])).
% 1.93/0.62  fof(f798,plain,(
% 1.93/0.62    spl8_3 <=> ! [X1] : ~r2_hidden(X1,sK2)),
% 1.93/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 1.93/0.62  fof(f801,plain,(
% 1.93/0.62    spl8_4 <=> ! [X0] : (r2_hidden(X0,sK4) | ~r2_hidden(X0,sK3))),
% 1.93/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 1.93/0.62  fof(f57,plain,(
% 1.93/0.62    spl8_1 <=> r1_tarski(k2_zfmisc_1(sK3,sK2),k2_zfmisc_1(sK4,sK2))),
% 1.93/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.93/0.62  fof(f977,plain,(
% 1.93/0.62    ( ! [X2,X3] : (r2_hidden(X2,sK4) | ~r2_hidden(X3,sK2) | ~r2_hidden(X2,sK3)) ) | ~spl8_1),
% 1.93/0.62    inference(resolution,[],[f59,f177])).
% 1.93/0.62  fof(f177,plain,(
% 1.93/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (~r1_tarski(k2_zfmisc_1(X2,X3),k2_zfmisc_1(X1,X4)) | r2_hidden(X0,X1) | ~r2_hidden(X5,X3) | ~r2_hidden(X0,X2)) )),
% 1.93/0.62    inference(resolution,[],[f105,f54])).
% 1.93/0.62  fof(f54,plain,(
% 1.93/0.62    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 1.93/0.62    inference(cnf_transformation,[],[f32])).
% 1.93/0.62  fof(f32,plain,(
% 1.93/0.62    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 1.93/0.62    inference(flattening,[],[f31])).
% 1.93/0.62  fof(f31,plain,(
% 1.93/0.62    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 1.93/0.62    inference(nnf_transformation,[],[f5])).
% 1.93/0.62  fof(f5,axiom,(
% 1.93/0.62    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 1.93/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 1.93/0.62  fof(f105,plain,(
% 1.93/0.62    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X2),X3) | r2_hidden(X0,X1) | ~r1_tarski(X3,k2_zfmisc_1(X1,X4))) )),
% 1.93/0.62    inference(resolution,[],[f52,f40])).
% 1.93/0.62  fof(f40,plain,(
% 1.93/0.62    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.93/0.62    inference(cnf_transformation,[],[f22])).
% 1.93/0.62  fof(f22,plain,(
% 1.93/0.62    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.93/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f20,f21])).
% 1.93/0.62  fof(f21,plain,(
% 1.93/0.62    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 1.93/0.62    introduced(choice_axiom,[])).
% 1.93/0.62  fof(f20,plain,(
% 1.93/0.62    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.93/0.62    inference(rectify,[],[f19])).
% 1.93/0.62  fof(f19,plain,(
% 1.93/0.62    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.93/0.62    inference(nnf_transformation,[],[f11])).
% 1.93/0.62  fof(f11,plain,(
% 1.93/0.62    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.93/0.62    inference(ennf_transformation,[],[f1])).
% 1.93/0.62  fof(f1,axiom,(
% 1.93/0.62    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.93/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.93/0.62  fof(f52,plain,(
% 1.93/0.62    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 1.93/0.62    inference(cnf_transformation,[],[f32])).
% 1.93/0.62  fof(f59,plain,(
% 1.93/0.62    r1_tarski(k2_zfmisc_1(sK3,sK2),k2_zfmisc_1(sK4,sK2)) | ~spl8_1),
% 1.93/0.62    inference(avatar_component_clause,[],[f57])).
% 1.93/0.62  fof(f975,plain,(
% 1.93/0.62    ~spl8_4),
% 1.93/0.62    inference(avatar_contradiction_clause,[],[f974])).
% 1.93/0.62  fof(f974,plain,(
% 1.93/0.62    $false | ~spl8_4),
% 1.93/0.62    inference(subsumption_resolution,[],[f973,f35])).
% 1.93/0.62  fof(f35,plain,(
% 1.93/0.62    ~r1_tarski(sK3,sK4)),
% 1.93/0.62    inference(cnf_transformation,[],[f16])).
% 1.93/0.62  fof(f16,plain,(
% 1.93/0.62    ~r1_tarski(sK3,sK4) & (r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK4)) | r1_tarski(k2_zfmisc_1(sK3,sK2),k2_zfmisc_1(sK4,sK2))) & k1_xboole_0 != sK2),
% 1.93/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f9,f15])).
% 1.93/0.62  fof(f15,plain,(
% 1.93/0.62    ? [X0,X1,X2] : (~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0) => (~r1_tarski(sK3,sK4) & (r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK4)) | r1_tarski(k2_zfmisc_1(sK3,sK2),k2_zfmisc_1(sK4,sK2))) & k1_xboole_0 != sK2)),
% 1.93/0.62    introduced(choice_axiom,[])).
% 1.93/0.62  fof(f9,plain,(
% 1.93/0.62    ? [X0,X1,X2] : (~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0)),
% 1.93/0.62    inference(ennf_transformation,[],[f7])).
% 1.93/0.62  fof(f7,negated_conjecture,(
% 1.93/0.62    ~! [X0,X1,X2] : ~(~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0)),
% 1.93/0.62    inference(negated_conjecture,[],[f6])).
% 1.93/0.62  fof(f6,conjecture,(
% 1.93/0.62    ! [X0,X1,X2] : ~(~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0)),
% 1.93/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).
% 1.93/0.62  fof(f973,plain,(
% 1.93/0.62    r1_tarski(sK3,sK4) | ~spl8_4),
% 1.93/0.62    inference(duplicate_literal_removal,[],[f971])).
% 1.93/0.62  fof(f971,plain,(
% 1.93/0.62    r1_tarski(sK3,sK4) | r1_tarski(sK3,sK4) | ~spl8_4),
% 1.93/0.62    inference(resolution,[],[f828,f41])).
% 1.93/0.62  fof(f41,plain,(
% 1.93/0.62    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.93/0.62    inference(cnf_transformation,[],[f22])).
% 1.93/0.62  fof(f828,plain,(
% 1.93/0.62    ( ! [X19] : (~r2_hidden(sK6(X19,sK4),sK3) | r1_tarski(X19,sK4)) ) | ~spl8_4),
% 1.93/0.62    inference(resolution,[],[f802,f42])).
% 1.93/0.62  fof(f42,plain,(
% 1.93/0.62    ( ! [X0,X1] : (~r2_hidden(sK6(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.93/0.62    inference(cnf_transformation,[],[f22])).
% 1.93/0.62  fof(f802,plain,(
% 1.93/0.62    ( ! [X0] : (r2_hidden(X0,sK4) | ~r2_hidden(X0,sK3)) ) | ~spl8_4),
% 1.93/0.62    inference(avatar_component_clause,[],[f801])).
% 1.93/0.62  fof(f821,plain,(
% 1.93/0.62    ~spl8_3),
% 1.93/0.62    inference(avatar_contradiction_clause,[],[f820])).
% 1.93/0.62  fof(f820,plain,(
% 1.93/0.62    $false | ~spl8_3),
% 1.93/0.62    inference(subsumption_resolution,[],[f819,f33])).
% 1.93/0.62  fof(f33,plain,(
% 1.93/0.62    k1_xboole_0 != sK2),
% 1.93/0.62    inference(cnf_transformation,[],[f16])).
% 1.93/0.62  fof(f819,plain,(
% 1.93/0.62    k1_xboole_0 = sK2 | ~spl8_3),
% 1.93/0.62    inference(resolution,[],[f807,f453])).
% 1.93/0.62  fof(f453,plain,(
% 1.93/0.62    ( ! [X20] : (~r1_tarski(X20,k1_xboole_0) | k1_xboole_0 = X20) )),
% 1.93/0.62    inference(resolution,[],[f385,f198])).
% 1.93/0.62  fof(f198,plain,(
% 1.93/0.62    ( ! [X2,X3] : (~sP1(X3,k1_xboole_0,X2) | k1_xboole_0 = X2) )),
% 1.93/0.62    inference(resolution,[],[f192,f86])).
% 1.93/0.62  fof(f86,plain,(
% 1.93/0.62    ( ! [X2,X0,X3,X1] : (~sP1(X0,X1,X3) | X2 = X3 | ~sP1(X0,X1,X2)) )),
% 1.93/0.62    inference(superposition,[],[f51,f51])).
% 1.93/0.62  fof(f51,plain,(
% 1.93/0.62    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~sP1(X0,X1,X2)) )),
% 1.93/0.62    inference(cnf_transformation,[],[f30])).
% 1.93/0.62  fof(f30,plain,(
% 1.93/0.62    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ~sP1(X0,X1,X2)) & (sP1(X0,X1,X2) | k3_xboole_0(X0,X1) != X2))),
% 1.93/0.62    inference(nnf_transformation,[],[f14])).
% 1.93/0.62  fof(f14,plain,(
% 1.93/0.62    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> sP1(X0,X1,X2))),
% 1.93/0.62    inference(definition_folding,[],[f2,f13,f12])).
% 1.93/0.62  fof(f12,plain,(
% 1.93/0.62    ! [X1,X3,X0] : (sP0(X1,X3,X0) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0)))),
% 1.93/0.62    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.93/0.62  fof(f13,plain,(
% 1.93/0.62    ! [X0,X1,X2] : (sP1(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP0(X1,X3,X0)))),
% 1.93/0.62    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.93/0.62  fof(f2,axiom,(
% 1.93/0.62    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.93/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.93/0.62  fof(f192,plain,(
% 1.93/0.62    ( ! [X0] : (sP1(X0,k1_xboole_0,k1_xboole_0)) )),
% 1.93/0.62    inference(resolution,[],[f186,f68])).
% 1.93/0.62  fof(f68,plain,(
% 1.93/0.62    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.93/0.62    inference(condensation,[],[f67])).
% 1.93/0.62  fof(f67,plain,(
% 1.93/0.62    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,X1)) )),
% 1.93/0.62    inference(resolution,[],[f39,f36])).
% 1.93/0.62  fof(f36,plain,(
% 1.93/0.62    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.93/0.62    inference(cnf_transformation,[],[f4])).
% 1.93/0.62  fof(f4,axiom,(
% 1.93/0.62    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.93/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.93/0.62  fof(f39,plain,(
% 1.93/0.62    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.93/0.62    inference(cnf_transformation,[],[f18])).
% 1.93/0.62  fof(f18,plain,(
% 1.93/0.62    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.93/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f10,f17])).
% 1.93/0.62  fof(f17,plain,(
% 1.93/0.62    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 1.93/0.62    introduced(choice_axiom,[])).
% 1.93/0.62  fof(f10,plain,(
% 1.93/0.62    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.93/0.62    inference(ennf_transformation,[],[f8])).
% 1.93/0.62  fof(f8,plain,(
% 1.93/0.62    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.93/0.62    inference(rectify,[],[f3])).
% 1.93/0.62  fof(f3,axiom,(
% 1.93/0.62    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.93/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.93/0.62  fof(f186,plain,(
% 1.93/0.62    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1,k1_xboole_0),X1) | sP1(X0,X1,k1_xboole_0)) )),
% 1.93/0.62    inference(resolution,[],[f139,f68])).
% 1.93/0.62  fof(f139,plain,(
% 1.93/0.62    ( ! [X2,X0,X1] : (r2_hidden(sK7(X0,X1,X2),X2) | sP1(X0,X1,X2) | r2_hidden(sK7(X0,X1,X2),X1)) )),
% 1.93/0.62    inference(resolution,[],[f45,f48])).
% 1.93/0.62  fof(f48,plain,(
% 1.93/0.62    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | r2_hidden(X1,X0)) )),
% 1.93/0.62    inference(cnf_transformation,[],[f29])).
% 1.93/0.62  fof(f29,plain,(
% 1.93/0.62    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ~r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) & ((r2_hidden(X1,X0) & r2_hidden(X1,X2)) | ~sP0(X0,X1,X2)))),
% 1.93/0.62    inference(rectify,[],[f28])).
% 1.93/0.62  fof(f28,plain,(
% 1.93/0.62    ! [X1,X3,X0] : ((sP0(X1,X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP0(X1,X3,X0)))),
% 1.93/0.62    inference(flattening,[],[f27])).
% 1.93/0.62  fof(f27,plain,(
% 1.93/0.62    ! [X1,X3,X0] : ((sP0(X1,X3,X0) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP0(X1,X3,X0)))),
% 1.93/0.62    inference(nnf_transformation,[],[f12])).
% 1.93/0.62  fof(f45,plain,(
% 1.93/0.62    ( ! [X2,X0,X1] : (sP0(X1,sK7(X0,X1,X2),X0) | sP1(X0,X1,X2) | r2_hidden(sK7(X0,X1,X2),X2)) )),
% 1.93/0.62    inference(cnf_transformation,[],[f26])).
% 1.93/0.62  fof(f26,plain,(
% 1.93/0.62    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ((~sP0(X1,sK7(X0,X1,X2),X0) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (sP0(X1,sK7(X0,X1,X2),X0) | r2_hidden(sK7(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X1,X4,X0)) & (sP0(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 1.93/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f24,f25])).
% 1.93/0.62  fof(f25,plain,(
% 1.93/0.62    ! [X2,X1,X0] : (? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2))) => ((~sP0(X1,sK7(X0,X1,X2),X0) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (sP0(X1,sK7(X0,X1,X2),X0) | r2_hidden(sK7(X0,X1,X2),X2))))),
% 1.93/0.62    introduced(choice_axiom,[])).
% 1.93/0.62  fof(f24,plain,(
% 1.93/0.62    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X1,X4,X0)) & (sP0(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 1.93/0.62    inference(rectify,[],[f23])).
% 1.93/0.62  fof(f23,plain,(
% 1.93/0.62    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP0(X1,X3,X0)) & (sP0(X1,X3,X0) | ~r2_hidden(X3,X2))) | ~sP1(X0,X1,X2)))),
% 1.93/0.62    inference(nnf_transformation,[],[f13])).
% 1.93/0.62  fof(f385,plain,(
% 1.93/0.62    ( ! [X10,X11] : (sP1(X10,X11,X10) | ~r1_tarski(X10,k1_xboole_0)) )),
% 1.93/0.62    inference(resolution,[],[f226,f75])).
% 1.93/0.62  fof(f75,plain,(
% 1.93/0.62    ( ! [X4,X3] : (~r2_hidden(X3,X4) | ~r1_tarski(X4,k1_xboole_0)) )),
% 1.93/0.62    inference(resolution,[],[f40,f68])).
% 1.93/0.62  fof(f226,plain,(
% 1.93/0.62    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1,X0),X0) | sP1(X0,X1,X0)) )),
% 1.93/0.62    inference(factoring,[],[f140])).
% 1.93/0.62  fof(f140,plain,(
% 1.93/0.62    ( ! [X4,X5,X3] : (r2_hidden(sK7(X3,X4,X5),X5) | sP1(X3,X4,X5) | r2_hidden(sK7(X3,X4,X5),X3)) )),
% 1.93/0.62    inference(resolution,[],[f45,f47])).
% 1.93/0.62  fof(f47,plain,(
% 1.93/0.62    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | r2_hidden(X1,X2)) )),
% 1.93/0.62    inference(cnf_transformation,[],[f29])).
% 1.93/0.62  fof(f807,plain,(
% 1.93/0.62    ( ! [X4] : (r1_tarski(sK2,X4)) ) | ~spl8_3),
% 1.93/0.62    inference(resolution,[],[f799,f41])).
% 1.93/0.62  fof(f799,plain,(
% 1.93/0.62    ( ! [X1] : (~r2_hidden(X1,sK2)) ) | ~spl8_3),
% 1.93/0.62    inference(avatar_component_clause,[],[f798])).
% 1.93/0.62  fof(f803,plain,(
% 1.93/0.62    spl8_3 | spl8_4 | ~spl8_2),
% 1.93/0.62    inference(avatar_split_clause,[],[f791,f61,f801,f798])).
% 1.93/0.62  fof(f61,plain,(
% 1.93/0.62    spl8_2 <=> r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK4))),
% 1.93/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.93/0.62  fof(f791,plain,(
% 1.93/0.62    ( ! [X0,X1] : (r2_hidden(X0,sK4) | ~r2_hidden(X0,sK3) | ~r2_hidden(X1,sK2)) ) | ~spl8_2),
% 1.93/0.62    inference(resolution,[],[f180,f63])).
% 1.93/0.62  fof(f63,plain,(
% 1.93/0.62    r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK4)) | ~spl8_2),
% 1.93/0.62    inference(avatar_component_clause,[],[f61])).
% 1.93/0.62  fof(f180,plain,(
% 1.93/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (~r1_tarski(k2_zfmisc_1(X2,X3),k2_zfmisc_1(X4,X1)) | r2_hidden(X0,X1) | ~r2_hidden(X0,X3) | ~r2_hidden(X5,X2)) )),
% 1.93/0.62    inference(resolution,[],[f106,f54])).
% 1.93/0.62  fof(f106,plain,(
% 1.93/0.62    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X2,X0),X3) | r2_hidden(X0,X1) | ~r1_tarski(X3,k2_zfmisc_1(X4,X1))) )),
% 1.93/0.62    inference(resolution,[],[f53,f40])).
% 1.93/0.62  fof(f53,plain,(
% 1.93/0.62    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 1.93/0.62    inference(cnf_transformation,[],[f32])).
% 1.93/0.62  fof(f64,plain,(
% 1.93/0.62    spl8_1 | spl8_2),
% 1.93/0.62    inference(avatar_split_clause,[],[f34,f61,f57])).
% 1.93/0.62  fof(f34,plain,(
% 1.93/0.62    r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,sK4)) | r1_tarski(k2_zfmisc_1(sK3,sK2),k2_zfmisc_1(sK4,sK2))),
% 1.93/0.62    inference(cnf_transformation,[],[f16])).
% 1.93/0.62  % SZS output end Proof for theBenchmark
% 1.93/0.62  % (18325)------------------------------
% 1.93/0.62  % (18325)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.93/0.62  % (18325)Termination reason: Refutation
% 1.93/0.62  
% 1.93/0.62  % (18325)Memory used [KB]: 6524
% 1.93/0.62  % (18325)Time elapsed: 0.199 s
% 1.93/0.62  % (18325)------------------------------
% 1.93/0.62  % (18325)------------------------------
% 1.93/0.62  % (18295)Success in time 0.254 s
%------------------------------------------------------------------------------
