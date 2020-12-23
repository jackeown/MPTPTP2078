%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 194 expanded)
%              Number of leaves         :   28 (  73 expanded)
%              Depth                    :   12
%              Number of atoms          :  345 ( 659 expanded)
%              Number of equality atoms :  190 ( 369 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f422,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f102,f111,f117,f124,f130,f150,f278,f298,f305,f306,f307,f420])).

fof(f420,plain,(
    ~ spl11_8 ),
    inference(avatar_contradiction_clause,[],[f392])).

fof(f392,plain,
    ( $false
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f82,f325])).

fof(f325,plain,
    ( ! [X0,X1] : X0 = X1
    | ~ spl11_8 ),
    inference(superposition,[],[f321,f321])).

fof(f321,plain,
    ( ! [X2] : sK1 = X2
    | ~ spl11_8 ),
    inference(resolution,[],[f149,f95])).

fof(f95,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_enumset1(X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f61,f71])).

fof(f71,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f70,f69])).

fof(f69,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f70,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK10(X0,X1) != X0
            | ~ r2_hidden(sK10(X0,X1),X1) )
          & ( sK10(X0,X1) = X0
            | r2_hidden(sK10(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f33,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK10(X0,X1) != X0
          | ~ r2_hidden(sK10(X0,X1),X1) )
        & ( sK10(X0,X1) = X0
          | r2_hidden(sK10(X0,X1),X1) ) ) ) ),
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f149,plain,
    ( ! [X3] : r2_hidden(sK1,X3)
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl11_8
  <=> ! [X3] : r2_hidden(sK1,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f82,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_enumset1(X0,X0,X0),X1) ),
    inference(definition_unfolding,[],[f68,f71])).

fof(f68,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f307,plain,
    ( k1_mcart_1(sK0) != sK1
    | sK0 != k1_mcart_1(sK0)
    | ~ r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0))
    | r2_hidden(sK1,k1_enumset1(sK0,sK0,sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f306,plain,
    ( k1_xboole_0 != k1_enumset1(sK0,sK0,sK0)
    | ~ r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0))
    | r2_hidden(sK0,k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f305,plain,(
    spl11_13 ),
    inference(avatar_contradiction_clause,[],[f299])).

fof(f299,plain,
    ( $false
    | spl11_13 ),
    inference(unit_resulting_resolution,[],[f89,f297])).

fof(f297,plain,
    ( ~ r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0))
    | spl11_13 ),
    inference(avatar_component_clause,[],[f295])).

fof(f295,plain,
    ( spl11_13
  <=> r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).

fof(f89,plain,(
    ! [X4,X0] : r2_hidden(X4,k1_enumset1(X0,X0,X4)) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k1_enumset1(X0,X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f57,f69])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK9(X0,X1,X2) != X1
              & sK9(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK9(X0,X1,X2),X2) )
          & ( sK9(X0,X1,X2) = X1
            | sK9(X0,X1,X2) = X0
            | r2_hidden(sK9(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f29,f30])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK9(X0,X1,X2) != X1
            & sK9(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK9(X0,X1,X2),X2) )
        & ( sK9(X0,X1,X2) = X1
          | sK9(X0,X1,X2) = X0
          | r2_hidden(sK9(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

% (28989)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
fof(f298,plain,
    ( spl11_11
    | ~ spl11_13
    | ~ spl11_6 ),
    inference(avatar_split_clause,[],[f293,f127,f295,f271])).

fof(f271,plain,
    ( spl11_11
  <=> k1_xboole_0 = k1_enumset1(sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).

fof(f127,plain,
    ( spl11_6
  <=> sK0 = k4_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f293,plain,
    ( ~ r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0))
    | k1_xboole_0 = k1_enumset1(sK0,sK0,sK0)
    | ~ spl11_6 ),
    inference(equality_resolution,[],[f268])).

fof(f268,plain,
    ( ! [X0] :
        ( sK0 != X0
        | ~ r2_hidden(sK0,k1_enumset1(X0,X0,X0))
        | k1_xboole_0 = k1_enumset1(X0,X0,X0) )
    | ~ spl11_6 ),
    inference(duplicate_literal_removal,[],[f259])).

fof(f259,plain,
    ( ! [X0] :
        ( sK0 != X0
        | ~ r2_hidden(sK0,k1_enumset1(X0,X0,X0))
        | k1_xboole_0 = k1_enumset1(X0,X0,X0)
        | k1_xboole_0 = k1_enumset1(X0,X0,X0) )
    | ~ spl11_6 ),
    inference(superposition,[],[f223,f155])).

fof(f155,plain,(
    ! [X2] :
      ( sK8(k1_enumset1(X2,X2,X2)) = X2
      | k1_xboole_0 = k1_enumset1(X2,X2,X2) ) ),
    inference(resolution,[],[f95,f52])).

fof(f52,plain,(
    ! [X0] :
      ( r2_hidden(sK8(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( ! [X2,X3] :
            ( k4_tarski(X2,X3) != sK8(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK8(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f15,f25])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] :
            ( k4_tarski(X2,X3) != sK8(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK8(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

fof(f223,plain,
    ( ! [X1] :
        ( sK0 != sK8(X1)
        | ~ r2_hidden(sK0,X1)
        | k1_xboole_0 = X1 )
    | ~ spl11_6 ),
    inference(superposition,[],[f54,f129])).

fof(f129,plain,
    ( sK0 = k4_tarski(sK1,sK0)
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f127])).

fof(f54,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK8(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f278,plain,
    ( spl11_11
    | ~ spl11_12
    | ~ spl11_1 ),
    inference(avatar_split_clause,[],[f269,f99,f275,f271])).

fof(f275,plain,
    ( spl11_12
  <=> r2_hidden(sK1,k1_enumset1(sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f99,plain,
    ( spl11_1
  <=> sK0 = k4_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f269,plain,
    ( ~ r2_hidden(sK1,k1_enumset1(sK0,sK0,sK0))
    | k1_xboole_0 = k1_enumset1(sK0,sK0,sK0)
    | ~ spl11_1 ),
    inference(equality_resolution,[],[f266])).

fof(f266,plain,
    ( ! [X4] :
        ( sK0 != X4
        | ~ r2_hidden(sK1,k1_enumset1(X4,X4,X4))
        | k1_xboole_0 = k1_enumset1(X4,X4,X4) )
    | ~ spl11_1 ),
    inference(duplicate_literal_removal,[],[f261])).

% (28989)Refutation not found, incomplete strategy% (28989)------------------------------
% (28989)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (28989)Termination reason: Refutation not found, incomplete strategy

% (28989)Memory used [KB]: 1663
% (28989)Time elapsed: 0.002 s
% (28989)------------------------------
% (28989)------------------------------
fof(f261,plain,
    ( ! [X4] :
        ( sK0 != X4
        | ~ r2_hidden(sK1,k1_enumset1(X4,X4,X4))
        | k1_xboole_0 = k1_enumset1(X4,X4,X4)
        | k1_xboole_0 = k1_enumset1(X4,X4,X4) )
    | ~ spl11_1 ),
    inference(superposition,[],[f220,f155])).

fof(f220,plain,
    ( ! [X0] :
        ( sK0 != sK8(X0)
        | ~ r2_hidden(sK1,X0)
        | k1_xboole_0 = X0 )
    | ~ spl11_1 ),
    inference(superposition,[],[f53,f101])).

fof(f101,plain,
    ( sK0 = k4_tarski(sK1,sK2)
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f99])).

fof(f53,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK8(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f150,plain,
    ( ~ spl11_7
    | spl11_8
    | ~ spl11_4 ),
    inference(avatar_split_clause,[],[f138,f114,f148,f144])).

fof(f144,plain,
    ( spl11_7
  <=> r2_hidden(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f114,plain,
    ( spl11_4
  <=> k1_mcart_1(sK0) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f138,plain,
    ( ! [X3] :
        ( r2_hidden(sK1,X3)
        | ~ r2_hidden(sK0,k1_xboole_0) )
    | ~ spl11_4 ),
    inference(superposition,[],[f134,f116])).

fof(f116,plain,
    ( k1_mcart_1(sK0) = sK1
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f114])).

fof(f134,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_mcart_1(X1),X0)
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f40,f96])).

fof(f96,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f130,plain,
    ( spl11_6
    | ~ spl11_1
    | ~ spl11_5 ),
    inference(avatar_split_clause,[],[f125,f121,f99,f127])).

fof(f121,plain,
    ( spl11_5
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f125,plain,
    ( sK0 = k4_tarski(sK1,sK0)
    | ~ spl11_1
    | ~ spl11_5 ),
    inference(superposition,[],[f101,f123])).

fof(f123,plain,
    ( sK0 = sK2
    | ~ spl11_5 ),
    inference(avatar_component_clause,[],[f121])).

fof(f124,plain,
    ( spl11_5
    | ~ spl11_1
    | ~ spl11_3 ),
    inference(avatar_split_clause,[],[f119,f108,f99,f121])).

fof(f108,plain,
    ( spl11_3
  <=> sK0 = k2_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f119,plain,
    ( sK0 = sK2
    | ~ spl11_1
    | ~ spl11_3 ),
    inference(forward_demodulation,[],[f118,f110])).

fof(f110,plain,
    ( sK0 = k2_mcart_1(sK0)
    | ~ spl11_3 ),
    inference(avatar_component_clause,[],[f108])).

fof(f118,plain,
    ( k2_mcart_1(sK0) = sK2
    | ~ spl11_1 ),
    inference(superposition,[],[f43,f101])).

fof(f43,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f117,plain,
    ( spl11_4
    | ~ spl11_1 ),
    inference(avatar_split_clause,[],[f112,f99,f114])).

fof(f112,plain,
    ( k1_mcart_1(sK0) = sK1
    | ~ spl11_1 ),
    inference(superposition,[],[f42,f101])).

fof(f42,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f111,plain,
    ( spl11_2
    | spl11_3 ),
    inference(avatar_split_clause,[],[f39,f108,f104])).

fof(f104,plain,
    ( spl11_2
  <=> sK0 = k1_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f39,plain,
    ( sK0 = k2_mcart_1(sK0)
    | sK0 = k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ( sK0 = k2_mcart_1(sK0)
      | sK0 = k1_mcart_1(sK0) )
    & sK0 = k4_tarski(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f17,f16])).

fof(f16,plain,
    ( ? [X0] :
        ( ( k2_mcart_1(X0) = X0
          | k1_mcart_1(X0) = X0 )
        & ? [X1,X2] : k4_tarski(X1,X2) = X0 )
   => ( ( sK0 = k2_mcart_1(sK0)
        | sK0 = k1_mcart_1(sK0) )
      & ? [X2,X1] : k4_tarski(X1,X2) = sK0 ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X2,X1] : k4_tarski(X1,X2) = sK0
   => sK0 = k4_tarski(sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ( k2_mcart_1(X0) = X0
        | k1_mcart_1(X0) = X0 )
      & ? [X1,X2] : k4_tarski(X1,X2) = X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ? [X1,X2] : k4_tarski(X1,X2) = X0
       => ( k2_mcart_1(X0) != X0
          & k1_mcart_1(X0) != X0 ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f102,plain,(
    spl11_1 ),
    inference(avatar_split_clause,[],[f38,f99])).

fof(f38,plain,(
    sK0 = k4_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:26:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (28962)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.51  % (28971)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.51  % (28964)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (28960)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (28983)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.52  % (28973)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.52  % (28972)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.53  % (28967)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.53  % (28975)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.53  % (28978)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.53  % (28982)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (28961)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (28986)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (28976)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.53  % (28986)Refutation not found, incomplete strategy% (28986)------------------------------
% 0.21/0.53  % (28986)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (28986)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (28986)Memory used [KB]: 6268
% 0.21/0.53  % (28986)Time elapsed: 0.121 s
% 0.21/0.53  % (28986)------------------------------
% 0.21/0.53  % (28986)------------------------------
% 0.21/0.53  % (28960)Refutation not found, incomplete strategy% (28960)------------------------------
% 0.21/0.53  % (28960)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (28960)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (28960)Memory used [KB]: 1791
% 0.21/0.53  % (28960)Time elapsed: 0.118 s
% 0.21/0.53  % (28960)------------------------------
% 0.21/0.53  % (28960)------------------------------
% 0.21/0.53  % (28959)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  % (28984)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.54  % (28963)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.54  % (28983)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f422,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f102,f111,f117,f124,f130,f150,f278,f298,f305,f306,f307,f420])).
% 0.21/0.54  fof(f420,plain,(
% 0.21/0.54    ~spl11_8),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f392])).
% 0.21/0.54  fof(f392,plain,(
% 0.21/0.54    $false | ~spl11_8),
% 0.21/0.54    inference(subsumption_resolution,[],[f82,f325])).
% 0.21/0.54  fof(f325,plain,(
% 0.21/0.54    ( ! [X0,X1] : (X0 = X1) ) | ~spl11_8),
% 0.21/0.54    inference(superposition,[],[f321,f321])).
% 0.21/0.54  fof(f321,plain,(
% 0.21/0.54    ( ! [X2] : (sK1 = X2) ) | ~spl11_8),
% 0.21/0.54    inference(resolution,[],[f149,f95])).
% 0.21/0.54  fof(f95,plain,(
% 0.21/0.54    ( ! [X0,X3] : (~r2_hidden(X3,k1_enumset1(X0,X0,X0)) | X0 = X3) )),
% 0.21/0.54    inference(equality_resolution,[],[f81])).
% 0.21/0.54  fof(f81,plain,(
% 0.21/0.54    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_enumset1(X0,X0,X0) != X1) )),
% 0.21/0.54    inference(definition_unfolding,[],[f61,f71])).
% 0.21/0.54  fof(f71,plain,(
% 0.21/0.54    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f70,f69])).
% 0.21/0.54  fof(f69,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.54  fof(f70,plain,(
% 0.21/0.54    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.54  fof(f61,plain,(
% 0.21/0.54    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f35])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK10(X0,X1) != X0 | ~r2_hidden(sK10(X0,X1),X1)) & (sK10(X0,X1) = X0 | r2_hidden(sK10(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f33,f34])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK10(X0,X1) != X0 | ~r2_hidden(sK10(X0,X1),X1)) & (sK10(X0,X1) = X0 | r2_hidden(sK10(X0,X1),X1))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.54    inference(rectify,[],[f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.54    inference(nnf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.21/0.54  fof(f149,plain,(
% 0.21/0.54    ( ! [X3] : (r2_hidden(sK1,X3)) ) | ~spl11_8),
% 0.21/0.54    inference(avatar_component_clause,[],[f148])).
% 0.21/0.54  fof(f148,plain,(
% 0.21/0.54    spl11_8 <=> ! [X3] : r2_hidden(sK1,X3)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).
% 0.21/0.54  fof(f82,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_enumset1(X0,X0,X0),X1)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f68,f71])).
% 0.21/0.54  fof(f68,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.21/0.54  fof(f307,plain,(
% 0.21/0.54    k1_mcart_1(sK0) != sK1 | sK0 != k1_mcart_1(sK0) | ~r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0)) | r2_hidden(sK1,k1_enumset1(sK0,sK0,sK0))),
% 0.21/0.54    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.54  fof(f306,plain,(
% 0.21/0.54    k1_xboole_0 != k1_enumset1(sK0,sK0,sK0) | ~r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0)) | r2_hidden(sK0,k1_xboole_0)),
% 0.21/0.54    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.54  fof(f305,plain,(
% 0.21/0.54    spl11_13),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f299])).
% 0.21/0.54  fof(f299,plain,(
% 0.21/0.54    $false | spl11_13),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f89,f297])).
% 0.21/0.54  fof(f297,plain,(
% 0.21/0.54    ~r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0)) | spl11_13),
% 0.21/0.54    inference(avatar_component_clause,[],[f295])).
% 0.21/0.54  fof(f295,plain,(
% 0.21/0.54    spl11_13 <=> r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).
% 0.21/0.54  fof(f89,plain,(
% 0.21/0.54    ( ! [X4,X0] : (r2_hidden(X4,k1_enumset1(X0,X0,X4))) )),
% 0.21/0.54    inference(equality_resolution,[],[f88])).
% 0.21/0.54  fof(f88,plain,(
% 0.21/0.54    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k1_enumset1(X0,X0,X4) != X2) )),
% 0.21/0.54    inference(equality_resolution,[],[f75])).
% 0.21/0.54  fof(f75,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k1_enumset1(X0,X0,X1) != X2) )),
% 0.21/0.54    inference(definition_unfolding,[],[f57,f69])).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 0.21/0.54    inference(cnf_transformation,[],[f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK9(X0,X1,X2) != X1 & sK9(X0,X1,X2) != X0) | ~r2_hidden(sK9(X0,X1,X2),X2)) & (sK9(X0,X1,X2) = X1 | sK9(X0,X1,X2) = X0 | r2_hidden(sK9(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f29,f30])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK9(X0,X1,X2) != X1 & sK9(X0,X1,X2) != X0) | ~r2_hidden(sK9(X0,X1,X2),X2)) & (sK9(X0,X1,X2) = X1 | sK9(X0,X1,X2) = X0 | r2_hidden(sK9(X0,X1,X2),X2))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.21/0.54    inference(rectify,[],[f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.21/0.54    inference(flattening,[],[f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.21/0.54    inference(nnf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 0.21/0.54  % (28989)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  fof(f298,plain,(
% 0.21/0.54    spl11_11 | ~spl11_13 | ~spl11_6),
% 0.21/0.54    inference(avatar_split_clause,[],[f293,f127,f295,f271])).
% 0.21/0.54  fof(f271,plain,(
% 0.21/0.54    spl11_11 <=> k1_xboole_0 = k1_enumset1(sK0,sK0,sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).
% 0.21/0.54  fof(f127,plain,(
% 0.21/0.54    spl11_6 <=> sK0 = k4_tarski(sK1,sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).
% 0.21/0.54  fof(f293,plain,(
% 0.21/0.54    ~r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0)) | k1_xboole_0 = k1_enumset1(sK0,sK0,sK0) | ~spl11_6),
% 0.21/0.54    inference(equality_resolution,[],[f268])).
% 0.21/0.54  fof(f268,plain,(
% 0.21/0.54    ( ! [X0] : (sK0 != X0 | ~r2_hidden(sK0,k1_enumset1(X0,X0,X0)) | k1_xboole_0 = k1_enumset1(X0,X0,X0)) ) | ~spl11_6),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f259])).
% 0.21/0.54  fof(f259,plain,(
% 0.21/0.54    ( ! [X0] : (sK0 != X0 | ~r2_hidden(sK0,k1_enumset1(X0,X0,X0)) | k1_xboole_0 = k1_enumset1(X0,X0,X0) | k1_xboole_0 = k1_enumset1(X0,X0,X0)) ) | ~spl11_6),
% 0.21/0.54    inference(superposition,[],[f223,f155])).
% 0.21/0.54  fof(f155,plain,(
% 0.21/0.54    ( ! [X2] : (sK8(k1_enumset1(X2,X2,X2)) = X2 | k1_xboole_0 = k1_enumset1(X2,X2,X2)) )),
% 0.21/0.54    inference(resolution,[],[f95,f52])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(sK8(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X0] : ((! [X2,X3] : (k4_tarski(X2,X3) != sK8(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK8(X0),X0)) | k1_xboole_0 = X0)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f15,f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X3,X2] : (k4_tarski(X2,X3) != sK8(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK8(X0),X0)))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.21/0.54    inference(ennf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,axiom,(
% 0.21/0.54    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).
% 0.21/0.54  fof(f223,plain,(
% 0.21/0.54    ( ! [X1] : (sK0 != sK8(X1) | ~r2_hidden(sK0,X1) | k1_xboole_0 = X1) ) | ~spl11_6),
% 0.21/0.54    inference(superposition,[],[f54,f129])).
% 0.21/0.54  fof(f129,plain,(
% 0.21/0.54    sK0 = k4_tarski(sK1,sK0) | ~spl11_6),
% 0.21/0.54    inference(avatar_component_clause,[],[f127])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK8(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f26])).
% 0.21/0.54  fof(f278,plain,(
% 0.21/0.54    spl11_11 | ~spl11_12 | ~spl11_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f269,f99,f275,f271])).
% 0.21/0.54  fof(f275,plain,(
% 0.21/0.54    spl11_12 <=> r2_hidden(sK1,k1_enumset1(sK0,sK0,sK0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).
% 0.21/0.54  fof(f99,plain,(
% 0.21/0.54    spl11_1 <=> sK0 = k4_tarski(sK1,sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 0.21/0.54  fof(f269,plain,(
% 0.21/0.54    ~r2_hidden(sK1,k1_enumset1(sK0,sK0,sK0)) | k1_xboole_0 = k1_enumset1(sK0,sK0,sK0) | ~spl11_1),
% 0.21/0.54    inference(equality_resolution,[],[f266])).
% 0.21/0.54  fof(f266,plain,(
% 0.21/0.54    ( ! [X4] : (sK0 != X4 | ~r2_hidden(sK1,k1_enumset1(X4,X4,X4)) | k1_xboole_0 = k1_enumset1(X4,X4,X4)) ) | ~spl11_1),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f261])).
% 0.21/0.54  % (28989)Refutation not found, incomplete strategy% (28989)------------------------------
% 0.21/0.54  % (28989)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (28989)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (28989)Memory used [KB]: 1663
% 0.21/0.54  % (28989)Time elapsed: 0.002 s
% 0.21/0.54  % (28989)------------------------------
% 0.21/0.54  % (28989)------------------------------
% 0.21/0.54  fof(f261,plain,(
% 0.21/0.54    ( ! [X4] : (sK0 != X4 | ~r2_hidden(sK1,k1_enumset1(X4,X4,X4)) | k1_xboole_0 = k1_enumset1(X4,X4,X4) | k1_xboole_0 = k1_enumset1(X4,X4,X4)) ) | ~spl11_1),
% 0.21/0.54    inference(superposition,[],[f220,f155])).
% 0.21/0.54  fof(f220,plain,(
% 0.21/0.54    ( ! [X0] : (sK0 != sK8(X0) | ~r2_hidden(sK1,X0) | k1_xboole_0 = X0) ) | ~spl11_1),
% 0.21/0.54    inference(superposition,[],[f53,f101])).
% 0.21/0.54  fof(f101,plain,(
% 0.21/0.54    sK0 = k4_tarski(sK1,sK2) | ~spl11_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f99])).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK8(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f26])).
% 0.21/0.54  fof(f150,plain,(
% 0.21/0.54    ~spl11_7 | spl11_8 | ~spl11_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f138,f114,f148,f144])).
% 0.21/0.54  fof(f144,plain,(
% 0.21/0.54    spl11_7 <=> r2_hidden(sK0,k1_xboole_0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).
% 0.21/0.54  fof(f114,plain,(
% 0.21/0.54    spl11_4 <=> k1_mcart_1(sK0) = sK1),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).
% 0.21/0.54  fof(f138,plain,(
% 0.21/0.54    ( ! [X3] : (r2_hidden(sK1,X3) | ~r2_hidden(sK0,k1_xboole_0)) ) | ~spl11_4),
% 0.21/0.54    inference(superposition,[],[f134,f116])).
% 0.21/0.54  fof(f116,plain,(
% 0.21/0.54    k1_mcart_1(sK0) = sK1 | ~spl11_4),
% 0.21/0.54    inference(avatar_component_clause,[],[f114])).
% 0.21/0.54  fof(f134,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(k1_mcart_1(X1),X0) | ~r2_hidden(X1,k1_xboole_0)) )),
% 0.21/0.54    inference(superposition,[],[f40,f96])).
% 0.21/0.54  fof(f96,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.54    inference(equality_resolution,[],[f67])).
% 0.21/0.54  fof(f67,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.21/0.54    inference(flattening,[],[f36])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.21/0.54    inference(nnf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.54    inference(ennf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.21/0.54  fof(f130,plain,(
% 0.21/0.54    spl11_6 | ~spl11_1 | ~spl11_5),
% 0.21/0.54    inference(avatar_split_clause,[],[f125,f121,f99,f127])).
% 0.21/0.54  fof(f121,plain,(
% 0.21/0.54    spl11_5 <=> sK0 = sK2),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).
% 0.21/0.54  fof(f125,plain,(
% 0.21/0.54    sK0 = k4_tarski(sK1,sK0) | (~spl11_1 | ~spl11_5)),
% 0.21/0.54    inference(superposition,[],[f101,f123])).
% 0.21/0.54  fof(f123,plain,(
% 0.21/0.54    sK0 = sK2 | ~spl11_5),
% 0.21/0.54    inference(avatar_component_clause,[],[f121])).
% 0.21/0.54  fof(f124,plain,(
% 0.21/0.54    spl11_5 | ~spl11_1 | ~spl11_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f119,f108,f99,f121])).
% 0.21/0.54  fof(f108,plain,(
% 0.21/0.54    spl11_3 <=> sK0 = k2_mcart_1(sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).
% 0.21/0.54  fof(f119,plain,(
% 0.21/0.54    sK0 = sK2 | (~spl11_1 | ~spl11_3)),
% 0.21/0.54    inference(forward_demodulation,[],[f118,f110])).
% 0.21/0.54  fof(f110,plain,(
% 0.21/0.54    sK0 = k2_mcart_1(sK0) | ~spl11_3),
% 0.21/0.54    inference(avatar_component_clause,[],[f108])).
% 0.21/0.54  fof(f118,plain,(
% 0.21/0.54    k2_mcart_1(sK0) = sK2 | ~spl11_1),
% 0.21/0.54    inference(superposition,[],[f43,f101])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.21/0.54  fof(f117,plain,(
% 0.21/0.54    spl11_4 | ~spl11_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f112,f99,f114])).
% 0.21/0.54  fof(f112,plain,(
% 0.21/0.54    k1_mcart_1(sK0) = sK1 | ~spl11_1),
% 0.21/0.54    inference(superposition,[],[f42,f101])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f9])).
% 0.21/0.54  fof(f111,plain,(
% 0.21/0.54    spl11_2 | spl11_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f39,f108,f104])).
% 0.21/0.54  fof(f104,plain,(
% 0.21/0.54    spl11_2 <=> sK0 = k1_mcart_1(sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    (sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)) & sK0 = k4_tarski(sK1,sK2)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f17,f16])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0) => ((sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)) & ? [X2,X1] : k4_tarski(X1,X2) = sK0)),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ? [X2,X1] : k4_tarski(X1,X2) = sK0 => sK0 = k4_tarski(sK1,sK2)),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f13,plain,(
% 0.21/0.54    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0)),
% 0.21/0.54    inference(ennf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,negated_conjecture,(
% 0.21/0.54    ~! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.21/0.54    inference(negated_conjecture,[],[f11])).
% 0.21/0.54  fof(f11,conjecture,(
% 0.21/0.54    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).
% 0.21/0.54  fof(f102,plain,(
% 0.21/0.54    spl11_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f38,f99])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    sK0 = k4_tarski(sK1,sK2)),
% 0.21/0.54    inference(cnf_transformation,[],[f18])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (28983)------------------------------
% 0.21/0.54  % (28983)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (28983)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (28983)Memory used [KB]: 11001
% 0.21/0.54  % (28983)Time elapsed: 0.066 s
% 0.21/0.54  % (28983)------------------------------
% 0.21/0.54  % (28983)------------------------------
% 0.21/0.54  % (28981)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.54  % (28974)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.55  % (28958)Success in time 0.181 s
%------------------------------------------------------------------------------
