%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:45 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 148 expanded)
%              Number of leaves         :   25 (  61 expanded)
%              Depth                    :   10
%              Number of atoms          :  258 ( 441 expanded)
%              Number of equality atoms :   48 (  57 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f427,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f59,f64,f82,f90,f281,f288,f309,f385,f396,f421,f423,f424])).

fof(f424,plain,
    ( k1_xboole_0 != sK3
    | ~ r2_hidden(sK6(sK3,sK3),sK3)
    | r2_hidden(sK6(k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f423,plain,(
    ~ spl7_32 ),
    inference(avatar_contradiction_clause,[],[f422])).

fof(f422,plain,
    ( $false
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f308,f343])).

fof(f343,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f35,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).

fof(f35,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f308,plain,
    ( r2_hidden(sK6(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ spl7_32 ),
    inference(avatar_component_clause,[],[f306])).

fof(f306,plain,
    ( spl7_32
  <=> r2_hidden(sK6(k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f421,plain,
    ( spl7_44
    | spl7_43 ),
    inference(avatar_split_clause,[],[f413,f393,f417])).

% (18728)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
fof(f417,plain,
    ( spl7_44
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).

fof(f393,plain,
    ( spl7_43
  <=> sP2(k1_setfam_1(sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).

fof(f413,plain,
    ( k1_xboole_0 = sK3
    | spl7_43 ),
    inference(resolution,[],[f395,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( sP2(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( sP2(X1,X0)
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 )
        | k1_xboole_0 != X0 )
      & ( sP2(X1,X0)
        | k1_xboole_0 = X0 ) ) ),
    inference(definition_folding,[],[f10,f15,f14,f13])).

fof(f13,plain,(
    ! [X2,X0] :
      ( sP0(X2,X0)
    <=> ! [X3] :
          ( r2_hidden(X2,X3)
          | ~ r2_hidden(X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f14,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> sP0(X2,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ( k1_setfam_1(X0) = X1
      <=> sP1(X0,X1) )
      | ~ sP2(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 )
        | k1_xboole_0 != X0 )
      & ( ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X2,X3)
                  | ~ r2_hidden(X3,X0) ) ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = X0
       => ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 ) )
      & ( k1_xboole_0 != X0
       => ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X3,X0)
                 => r2_hidden(X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_setfam_1)).

fof(f395,plain,
    ( ~ sP2(k1_setfam_1(sK3),sK3)
    | spl7_43 ),
    inference(avatar_component_clause,[],[f393])).

fof(f396,plain,
    ( ~ spl7_43
    | spl7_41 ),
    inference(avatar_split_clause,[],[f391,f382,f393])).

fof(f382,plain,
    ( spl7_41
  <=> sP1(sK3,k1_setfam_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).

fof(f391,plain,
    ( ~ sP2(k1_setfam_1(sK3),sK3)
    | spl7_41 ),
    inference(unit_resulting_resolution,[],[f384,f50])).

fof(f50,plain,(
    ! [X1] :
      ( ~ sP2(k1_setfam_1(X1),X1)
      | sP1(X1,k1_setfam_1(X1)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( sP1(X1,X0)
      | k1_setfam_1(X1) != X0
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ( k1_setfam_1(X1) = X0
          | ~ sP1(X1,X0) )
        & ( sP1(X1,X0)
          | k1_setfam_1(X1) != X0 ) )
      | ~ sP2(X0,X1) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ( ( k1_setfam_1(X0) = X1
          | ~ sP1(X0,X1) )
        & ( sP1(X0,X1)
          | k1_setfam_1(X0) != X1 ) )
      | ~ sP2(X1,X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f384,plain,
    ( ~ sP1(sK3,k1_setfam_1(sK3))
    | spl7_41 ),
    inference(avatar_component_clause,[],[f382])).

fof(f385,plain,
    ( ~ spl7_41
    | ~ spl7_2
    | ~ spl7_5
    | ~ spl7_31 ),
    inference(avatar_split_clause,[],[f378,f298,f87,f61,f382])).

fof(f61,plain,
    ( spl7_2
  <=> r2_hidden(k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f87,plain,
    ( spl7_5
  <=> r2_hidden(sK4(k1_setfam_1(sK3)),k1_setfam_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f298,plain,
    ( spl7_31
  <=> sP0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f378,plain,
    ( ~ sP1(sK3,k1_setfam_1(sK3))
    | ~ spl7_2
    | ~ spl7_5
    | ~ spl7_31 ),
    inference(unit_resulting_resolution,[],[f89,f359,f38])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( ~ sP1(X0,X1)
      | ~ r2_hidden(X3,X1)
      | sP0(X3,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ( ( ~ sP0(sK5(X0,X1),X0)
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( sP0(sK5(X0,X1),X0)
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ sP0(X3,X0) )
            & ( sP0(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP1(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f24,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ sP0(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( sP0(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ sP0(sK5(X0,X1),X0)
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( sP0(sK5(X0,X1),X0)
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ? [X2] :
            ( ( ~ sP0(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( sP0(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ sP0(X3,X0) )
            & ( sP0(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP1(X0,X1) ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ? [X2] :
            ( ( ~ sP0(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( sP0(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ sP0(X2,X0) )
            & ( sP0(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | ~ sP1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f359,plain,
    ( ! [X0] : ~ sP0(X0,sK3)
    | ~ spl7_2
    | ~ spl7_31 ),
    inference(unit_resulting_resolution,[],[f63,f340,f42])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( ~ sP0(X0,X1)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X0,X3) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ~ r2_hidden(X0,sK6(X0,X1))
          & r2_hidden(sK6(X0,X1),X1) ) )
      & ( ! [X3] :
            ( r2_hidden(X0,X3)
            | ~ r2_hidden(X3,X1) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f28,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X0,X2)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(X0,sK6(X0,X1))
        & r2_hidden(sK6(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X0,X2)
            & r2_hidden(X2,X1) ) )
      & ( ! [X3] :
            ( r2_hidden(X0,X3)
            | ~ r2_hidden(X3,X1) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X2,X0] :
      ( ( sP0(X2,X0)
        | ? [X3] :
            ( ~ r2_hidden(X2,X3)
            & r2_hidden(X3,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X2,X3)
            | ~ r2_hidden(X3,X0) )
        | ~ sP0(X2,X0) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f340,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl7_31 ),
    inference(subsumption_resolution,[],[f324,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f324,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | r2_hidden(k1_xboole_0,X0) )
    | ~ spl7_31 ),
    inference(resolution,[],[f299,f42])).

fof(f299,plain,
    ( sP0(k1_xboole_0,k1_xboole_0)
    | ~ spl7_31 ),
    inference(avatar_component_clause,[],[f298])).

fof(f63,plain,
    ( r2_hidden(k1_xboole_0,sK3)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f89,plain,
    ( r2_hidden(sK4(k1_setfam_1(sK3)),k1_setfam_1(sK3))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f87])).

fof(f309,plain,
    ( spl7_32
    | spl7_31 ),
    inference(avatar_split_clause,[],[f304,f298,f306])).

fof(f304,plain,
    ( r2_hidden(sK6(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | spl7_31 ),
    inference(unit_resulting_resolution,[],[f300,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X1)
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f300,plain,
    ( ~ sP0(k1_xboole_0,k1_xboole_0)
    | spl7_31 ),
    inference(avatar_component_clause,[],[f298])).

fof(f288,plain,
    ( spl7_29
    | spl7_28 ),
    inference(avatar_split_clause,[],[f283,f278,f285])).

fof(f285,plain,
    ( spl7_29
  <=> r2_hidden(sK6(sK3,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).

fof(f278,plain,
    ( spl7_28
  <=> sP0(sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f283,plain,
    ( r2_hidden(sK6(sK3,sK3),sK3)
    | spl7_28 ),
    inference(unit_resulting_resolution,[],[f280,f43])).

fof(f280,plain,
    ( ~ sP0(sK3,sK3)
    | spl7_28 ),
    inference(avatar_component_clause,[],[f278])).

fof(f281,plain,
    ( ~ spl7_28
    | ~ spl7_2
    | spl7_4 ),
    inference(avatar_split_clause,[],[f250,f77,f61,f278])).

fof(f77,plain,
    ( spl7_4
  <=> r2_hidden(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f250,plain,
    ( ~ sP0(sK3,sK3)
    | ~ spl7_2
    | spl7_4 ),
    inference(unit_resulting_resolution,[],[f79,f63,f42])).

fof(f79,plain,
    ( ~ r2_hidden(sK3,k1_xboole_0)
    | spl7_4 ),
    inference(avatar_component_clause,[],[f77])).

fof(f90,plain,
    ( spl7_5
    | spl7_1 ),
    inference(avatar_split_clause,[],[f83,f56,f87])).

fof(f56,plain,
    ( spl7_1
  <=> k1_xboole_0 = k1_setfam_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f83,plain,
    ( r2_hidden(sK4(k1_setfam_1(sK3)),k1_setfam_1(sK3))
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f58,f34])).

fof(f34,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f9,f19])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f58,plain,
    ( k1_xboole_0 != k1_setfam_1(sK3)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f82,plain,
    ( ~ spl7_4
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f75,f61,f77])).

fof(f75,plain,
    ( ~ r2_hidden(sK3,k1_xboole_0)
    | ~ spl7_2 ),
    inference(resolution,[],[f48,f63])).

fof(f64,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f32,f61])).

fof(f32,plain,(
    r2_hidden(k1_xboole_0,sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( k1_xboole_0 != k1_setfam_1(sK3)
    & r2_hidden(k1_xboole_0,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f8,f17])).

fof(f17,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k1_setfam_1(X0)
        & r2_hidden(k1_xboole_0,X0) )
   => ( k1_xboole_0 != k1_setfam_1(sK3)
      & r2_hidden(k1_xboole_0,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( k1_xboole_0 != k1_setfam_1(X0)
      & r2_hidden(k1_xboole_0,X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( r2_hidden(k1_xboole_0,X0)
       => k1_xboole_0 = k1_setfam_1(X0) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,X0)
     => k1_xboole_0 = k1_setfam_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_setfam_1)).

fof(f59,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f33,f56])).

fof(f33,plain,(
    k1_xboole_0 != k1_setfam_1(sK3) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:47:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (18730)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.47  % (18730)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % (18719)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.47  % (18724)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.48  % (18727)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.48  % (18727)Refutation not found, incomplete strategy% (18727)------------------------------
% 0.21/0.48  % (18727)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (18727)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (18727)Memory used [KB]: 1663
% 0.21/0.48  % (18727)Time elapsed: 0.060 s
% 0.21/0.48  % (18727)------------------------------
% 0.21/0.48  % (18727)------------------------------
% 0.21/0.48  % (18717)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f427,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f59,f64,f82,f90,f281,f288,f309,f385,f396,f421,f423,f424])).
% 0.21/0.49  fof(f424,plain,(
% 0.21/0.49    k1_xboole_0 != sK3 | ~r2_hidden(sK6(sK3,sK3),sK3) | r2_hidden(sK6(k1_xboole_0,k1_xboole_0),k1_xboole_0)),
% 0.21/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.49  fof(f423,plain,(
% 0.21/0.49    ~spl7_32),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f422])).
% 0.21/0.49  fof(f422,plain,(
% 0.21/0.49    $false | ~spl7_32),
% 0.21/0.49    inference(subsumption_resolution,[],[f308,f343])).
% 0.21/0.49  fof(f343,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f35,f49])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.21/0.49  fof(f308,plain,(
% 0.21/0.49    r2_hidden(sK6(k1_xboole_0,k1_xboole_0),k1_xboole_0) | ~spl7_32),
% 0.21/0.49    inference(avatar_component_clause,[],[f306])).
% 0.21/0.49  fof(f306,plain,(
% 0.21/0.49    spl7_32 <=> r2_hidden(sK6(k1_xboole_0,k1_xboole_0),k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).
% 0.21/0.49  fof(f421,plain,(
% 0.21/0.49    spl7_44 | spl7_43),
% 0.21/0.49    inference(avatar_split_clause,[],[f413,f393,f417])).
% 0.21/0.49  % (18728)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  fof(f417,plain,(
% 0.21/0.49    spl7_44 <=> k1_xboole_0 = sK3),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).
% 0.21/0.49  fof(f393,plain,(
% 0.21/0.49    spl7_43 <=> sP2(k1_setfam_1(sK3),sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).
% 0.21/0.49  fof(f413,plain,(
% 0.21/0.49    k1_xboole_0 = sK3 | spl7_43),
% 0.21/0.49    inference(resolution,[],[f395,f45])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ( ! [X0,X1] : (sP2(X1,X0) | k1_xboole_0 = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ! [X0,X1] : ((((k1_setfam_1(X0) = X1 | k1_xboole_0 != X1) & (k1_xboole_0 = X1 | k1_setfam_1(X0) != X1)) | k1_xboole_0 != X0) & (sP2(X1,X0) | k1_xboole_0 = X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0,X1] : (((k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1) | k1_xboole_0 != X0) & (sP2(X1,X0) | k1_xboole_0 = X0))),
% 0.21/0.49    inference(definition_folding,[],[f10,f15,f14,f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X2,X0] : (sP0(X2,X0) <=> ! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)))),
% 0.21/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0,X1] : (sP1(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> sP0(X2,X0)))),
% 0.21/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X1,X0] : ((k1_setfam_1(X0) = X1 <=> sP1(X0,X1)) | ~sP2(X1,X0))),
% 0.21/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ! [X0,X1] : (((k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1) | k1_xboole_0 != X0) & ((k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)))) | k1_xboole_0 = X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1] : ((k1_xboole_0 = X0 => (k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1)) & (k1_xboole_0 != X0 => (k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X3,X0) => r2_hidden(X2,X3))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_setfam_1)).
% 0.21/0.49  fof(f395,plain,(
% 0.21/0.49    ~sP2(k1_setfam_1(sK3),sK3) | spl7_43),
% 0.21/0.49    inference(avatar_component_clause,[],[f393])).
% 0.21/0.49  fof(f396,plain,(
% 0.21/0.49    ~spl7_43 | spl7_41),
% 0.21/0.49    inference(avatar_split_clause,[],[f391,f382,f393])).
% 0.21/0.49  fof(f382,plain,(
% 0.21/0.49    spl7_41 <=> sP1(sK3,k1_setfam_1(sK3))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).
% 0.21/0.49  fof(f391,plain,(
% 0.21/0.49    ~sP2(k1_setfam_1(sK3),sK3) | spl7_41),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f384,f50])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ( ! [X1] : (~sP2(k1_setfam_1(X1),X1) | sP1(X1,k1_setfam_1(X1))) )),
% 0.21/0.49    inference(equality_resolution,[],[f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ( ! [X0,X1] : (sP1(X1,X0) | k1_setfam_1(X1) != X0 | ~sP2(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0,X1] : (((k1_setfam_1(X1) = X0 | ~sP1(X1,X0)) & (sP1(X1,X0) | k1_setfam_1(X1) != X0)) | ~sP2(X0,X1))),
% 0.21/0.49    inference(rectify,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X1,X0] : (((k1_setfam_1(X0) = X1 | ~sP1(X0,X1)) & (sP1(X0,X1) | k1_setfam_1(X0) != X1)) | ~sP2(X1,X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f15])).
% 0.21/0.49  fof(f384,plain,(
% 0.21/0.49    ~sP1(sK3,k1_setfam_1(sK3)) | spl7_41),
% 0.21/0.49    inference(avatar_component_clause,[],[f382])).
% 0.21/0.49  fof(f385,plain,(
% 0.21/0.49    ~spl7_41 | ~spl7_2 | ~spl7_5 | ~spl7_31),
% 0.21/0.49    inference(avatar_split_clause,[],[f378,f298,f87,f61,f382])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    spl7_2 <=> r2_hidden(k1_xboole_0,sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    spl7_5 <=> r2_hidden(sK4(k1_setfam_1(sK3)),k1_setfam_1(sK3))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.49  fof(f298,plain,(
% 0.21/0.49    spl7_31 <=> sP0(k1_xboole_0,k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).
% 0.21/0.49  fof(f378,plain,(
% 0.21/0.49    ~sP1(sK3,k1_setfam_1(sK3)) | (~spl7_2 | ~spl7_5 | ~spl7_31)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f89,f359,f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ( ! [X0,X3,X1] : (~sP1(X0,X1) | ~r2_hidden(X3,X1) | sP0(X3,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0,X1] : ((sP1(X0,X1) | ((~sP0(sK5(X0,X1),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (sP0(sK5(X0,X1),X0) | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~sP0(X3,X0)) & (sP0(X3,X0) | ~r2_hidden(X3,X1))) | ~sP1(X0,X1)))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f24,f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X1,X0] : (? [X2] : ((~sP0(X2,X0) | ~r2_hidden(X2,X1)) & (sP0(X2,X0) | r2_hidden(X2,X1))) => ((~sP0(sK5(X0,X1),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (sP0(sK5(X0,X1),X0) | r2_hidden(sK5(X0,X1),X1))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0,X1] : ((sP1(X0,X1) | ? [X2] : ((~sP0(X2,X0) | ~r2_hidden(X2,X1)) & (sP0(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~sP0(X3,X0)) & (sP0(X3,X0) | ~r2_hidden(X3,X1))) | ~sP1(X0,X1)))),
% 0.21/0.49    inference(rectify,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0,X1] : ((sP1(X0,X1) | ? [X2] : ((~sP0(X2,X0) | ~r2_hidden(X2,X1)) & (sP0(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~sP0(X2,X0)) & (sP0(X2,X0) | ~r2_hidden(X2,X1))) | ~sP1(X0,X1)))),
% 0.21/0.49    inference(nnf_transformation,[],[f14])).
% 0.21/0.49  fof(f359,plain,(
% 0.21/0.49    ( ! [X0] : (~sP0(X0,sK3)) ) | (~spl7_2 | ~spl7_31)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f63,f340,f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ( ! [X0,X3,X1] : (~sP0(X0,X1) | ~r2_hidden(X3,X1) | r2_hidden(X0,X3)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ! [X0,X1] : ((sP0(X0,X1) | (~r2_hidden(X0,sK6(X0,X1)) & r2_hidden(sK6(X0,X1),X1))) & (! [X3] : (r2_hidden(X0,X3) | ~r2_hidden(X3,X1)) | ~sP0(X0,X1)))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f28,f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X0,X2) & r2_hidden(X2,X1)) => (~r2_hidden(X0,sK6(X0,X1)) & r2_hidden(sK6(X0,X1),X1)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (~r2_hidden(X0,X2) & r2_hidden(X2,X1))) & (! [X3] : (r2_hidden(X0,X3) | ~r2_hidden(X3,X1)) | ~sP0(X0,X1)))),
% 0.21/0.49    inference(rectify,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X2,X0] : ((sP0(X2,X0) | ? [X3] : (~r2_hidden(X2,X3) & r2_hidden(X3,X0))) & (! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)) | ~sP0(X2,X0)))),
% 0.21/0.49    inference(nnf_transformation,[],[f13])).
% 0.21/0.49  fof(f340,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl7_31),
% 0.21/0.49    inference(subsumption_resolution,[],[f324,f48])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 0.21/0.49  fof(f324,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | r2_hidden(k1_xboole_0,X0)) ) | ~spl7_31),
% 0.21/0.49    inference(resolution,[],[f299,f42])).
% 0.21/0.49  fof(f299,plain,(
% 0.21/0.49    sP0(k1_xboole_0,k1_xboole_0) | ~spl7_31),
% 0.21/0.49    inference(avatar_component_clause,[],[f298])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    r2_hidden(k1_xboole_0,sK3) | ~spl7_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f61])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    r2_hidden(sK4(k1_setfam_1(sK3)),k1_setfam_1(sK3)) | ~spl7_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f87])).
% 0.21/0.49  fof(f309,plain,(
% 0.21/0.49    spl7_32 | spl7_31),
% 0.21/0.49    inference(avatar_split_clause,[],[f304,f298,f306])).
% 0.21/0.49  fof(f304,plain,(
% 0.21/0.49    r2_hidden(sK6(k1_xboole_0,k1_xboole_0),k1_xboole_0) | spl7_31),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f300,f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X1) | sP0(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f30])).
% 0.21/0.49  fof(f300,plain,(
% 0.21/0.49    ~sP0(k1_xboole_0,k1_xboole_0) | spl7_31),
% 0.21/0.49    inference(avatar_component_clause,[],[f298])).
% 0.21/0.49  fof(f288,plain,(
% 0.21/0.49    spl7_29 | spl7_28),
% 0.21/0.49    inference(avatar_split_clause,[],[f283,f278,f285])).
% 0.21/0.49  fof(f285,plain,(
% 0.21/0.49    spl7_29 <=> r2_hidden(sK6(sK3,sK3),sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).
% 0.21/0.49  fof(f278,plain,(
% 0.21/0.49    spl7_28 <=> sP0(sK3,sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).
% 0.21/0.49  fof(f283,plain,(
% 0.21/0.49    r2_hidden(sK6(sK3,sK3),sK3) | spl7_28),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f280,f43])).
% 0.21/0.49  fof(f280,plain,(
% 0.21/0.49    ~sP0(sK3,sK3) | spl7_28),
% 0.21/0.49    inference(avatar_component_clause,[],[f278])).
% 0.21/0.49  fof(f281,plain,(
% 0.21/0.49    ~spl7_28 | ~spl7_2 | spl7_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f250,f77,f61,f278])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    spl7_4 <=> r2_hidden(sK3,k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.49  fof(f250,plain,(
% 0.21/0.49    ~sP0(sK3,sK3) | (~spl7_2 | spl7_4)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f79,f63,f42])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    ~r2_hidden(sK3,k1_xboole_0) | spl7_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f77])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    spl7_5 | spl7_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f83,f56,f87])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    spl7_1 <=> k1_xboole_0 = k1_setfam_1(sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    r2_hidden(sK4(k1_setfam_1(sK3)),k1_setfam_1(sK3)) | spl7_1),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f58,f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f9,f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    k1_xboole_0 != k1_setfam_1(sK3) | spl7_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f56])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    ~spl7_4 | ~spl7_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f75,f61,f77])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    ~r2_hidden(sK3,k1_xboole_0) | ~spl7_2),
% 0.21/0.49    inference(resolution,[],[f48,f63])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    spl7_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f32,f61])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    r2_hidden(k1_xboole_0,sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    k1_xboole_0 != k1_setfam_1(sK3) & r2_hidden(k1_xboole_0,sK3)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f8,f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ? [X0] : (k1_xboole_0 != k1_setfam_1(X0) & r2_hidden(k1_xboole_0,X0)) => (k1_xboole_0 != k1_setfam_1(sK3) & r2_hidden(k1_xboole_0,sK3))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    ? [X0] : (k1_xboole_0 != k1_setfam_1(X0) & r2_hidden(k1_xboole_0,X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,negated_conjecture,(
% 0.21/0.49    ~! [X0] : (r2_hidden(k1_xboole_0,X0) => k1_xboole_0 = k1_setfam_1(X0))),
% 0.21/0.49    inference(negated_conjecture,[],[f6])).
% 0.21/0.49  fof(f6,conjecture,(
% 0.21/0.49    ! [X0] : (r2_hidden(k1_xboole_0,X0) => k1_xboole_0 = k1_setfam_1(X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_setfam_1)).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    ~spl7_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f33,f56])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    k1_xboole_0 != k1_setfam_1(sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (18730)------------------------------
% 0.21/0.49  % (18730)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (18730)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (18730)Memory used [KB]: 10874
% 0.21/0.49  % (18730)Time elapsed: 0.061 s
% 0.21/0.49  % (18730)------------------------------
% 0.21/0.49  % (18730)------------------------------
% 0.21/0.49  % (18712)Success in time 0.125 s
%------------------------------------------------------------------------------
