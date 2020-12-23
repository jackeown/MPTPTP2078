%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0376+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:51 EST 2020

% Result     : Theorem 1.38s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 170 expanded)
%              Number of leaves         :   34 (  78 expanded)
%              Depth                    :   10
%              Number of atoms          :  425 ( 839 expanded)
%              Number of equality atoms :  146 ( 213 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f798,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f79,f84,f89,f94,f99,f104,f158,f221,f288,f314,f319,f336,f792,f794,f795,f796,f797])).

fof(f797,plain,
    ( sK4 != sK5(k2_enumset1(sK1,sK2,sK3,sK4),sK0)
    | ~ m1_subset_1(sK4,sK0)
    | m1_subset_1(sK5(k2_enumset1(sK1,sK2,sK3,sK4),sK0),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f796,plain,
    ( sK3 != sK5(k2_enumset1(sK1,sK2,sK3,sK4),sK0)
    | ~ m1_subset_1(sK3,sK0)
    | m1_subset_1(sK5(k2_enumset1(sK1,sK2,sK3,sK4),sK0),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f795,plain,
    ( sK2 != sK5(k2_enumset1(sK1,sK2,sK3,sK4),sK0)
    | ~ m1_subset_1(sK2,sK0)
    | m1_subset_1(sK5(k2_enumset1(sK1,sK2,sK3,sK4),sK0),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f794,plain,
    ( sK1 != sK5(k2_enumset1(sK1,sK2,sK3,sK4),sK0)
    | ~ m1_subset_1(sK1,sK0)
    | m1_subset_1(sK5(k2_enumset1(sK1,sK2,sK3,sK4),sK0),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f792,plain,
    ( spl8_21
    | spl8_22
    | spl8_23
    | spl8_24
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f765,f316,f789,f785,f781,f777])).

fof(f777,plain,
    ( spl8_21
  <=> sK1 = sK5(k2_enumset1(sK1,sK2,sK3,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f781,plain,
    ( spl8_22
  <=> sK2 = sK5(k2_enumset1(sK1,sK2,sK3,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f785,plain,
    ( spl8_23
  <=> sK3 = sK5(k2_enumset1(sK1,sK2,sK3,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f789,plain,
    ( spl8_24
  <=> sK4 = sK5(k2_enumset1(sK1,sK2,sK3,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f316,plain,
    ( spl8_19
  <=> r2_hidden(sK5(k2_enumset1(sK1,sK2,sK3,sK4),sK0),k2_enumset1(sK1,sK2,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f765,plain,
    ( sK4 = sK5(k2_enumset1(sK1,sK2,sK3,sK4),sK0)
    | sK3 = sK5(k2_enumset1(sK1,sK2,sK3,sK4),sK0)
    | sK2 = sK5(k2_enumset1(sK1,sK2,sK3,sK4),sK0)
    | sK1 = sK5(k2_enumset1(sK1,sK2,sK3,sK4),sK0)
    | ~ spl8_19 ),
    inference(resolution,[],[f318,f74])).

fof(f74,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( X3 = X6
      | X2 = X6
      | X1 = X6
      | X0 = X6
      | ~ r2_hidden(X6,k2_enumset1(X0,X1,X2,X3)) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( X3 = X6
      | X2 = X6
      | X1 = X6
      | X0 = X6
      | ~ r2_hidden(X6,X4)
      | k2_enumset1(X0,X1,X2,X3) != X4 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_enumset1(X0,X1,X2,X3) = X4
        | ( ( ( sK7(X0,X1,X2,X3,X4) != X3
              & sK7(X0,X1,X2,X3,X4) != X2
              & sK7(X0,X1,X2,X3,X4) != X1
              & sK7(X0,X1,X2,X3,X4) != X0 )
            | ~ r2_hidden(sK7(X0,X1,X2,X3,X4),X4) )
          & ( sK7(X0,X1,X2,X3,X4) = X3
            | sK7(X0,X1,X2,X3,X4) = X2
            | sK7(X0,X1,X2,X3,X4) = X1
            | sK7(X0,X1,X2,X3,X4) = X0
            | r2_hidden(sK7(X0,X1,X2,X3,X4),X4) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X4)
              | ( X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 ) )
            & ( X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | ~ r2_hidden(X6,X4) ) )
        | k2_enumset1(X0,X1,X2,X3) != X4 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f32,f33])).

fof(f33,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( ( ( X3 != X5
              & X2 != X5
              & X1 != X5
              & X0 != X5 )
            | ~ r2_hidden(X5,X4) )
          & ( X3 = X5
            | X2 = X5
            | X1 = X5
            | X0 = X5
            | r2_hidden(X5,X4) ) )
     => ( ( ( sK7(X0,X1,X2,X3,X4) != X3
            & sK7(X0,X1,X2,X3,X4) != X2
            & sK7(X0,X1,X2,X3,X4) != X1
            & sK7(X0,X1,X2,X3,X4) != X0 )
          | ~ r2_hidden(sK7(X0,X1,X2,X3,X4),X4) )
        & ( sK7(X0,X1,X2,X3,X4) = X3
          | sK7(X0,X1,X2,X3,X4) = X2
          | sK7(X0,X1,X2,X3,X4) = X1
          | sK7(X0,X1,X2,X3,X4) = X0
          | r2_hidden(sK7(X0,X1,X2,X3,X4),X4) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_enumset1(X0,X1,X2,X3) = X4
        | ? [X5] :
            ( ( ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 )
              | ~ r2_hidden(X5,X4) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X4)
              | ( X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 ) )
            & ( X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | ~ r2_hidden(X6,X4) ) )
        | k2_enumset1(X0,X1,X2,X3) != X4 ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_enumset1(X0,X1,X2,X3) = X4
        | ? [X5] :
            ( ( ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 )
              | ~ r2_hidden(X5,X4) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X4)
              | ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X4) ) )
        | k2_enumset1(X0,X1,X2,X3) != X4 ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_enumset1(X0,X1,X2,X3) = X4
        | ? [X5] :
            ( ( ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 )
              | ~ r2_hidden(X5,X4) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X4)
              | ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X4) ) )
        | k2_enumset1(X0,X1,X2,X3) != X4 ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ( X3 = X5
            | X2 = X5
            | X1 = X5
            | X0 = X5 ) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X3 != X5
              & X2 != X5
              & X1 != X5
              & X0 != X5 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_enumset1)).

fof(f318,plain,
    ( r2_hidden(sK5(k2_enumset1(sK1,sK2,sK3,sK4),sK0),k2_enumset1(sK1,sK2,sK3,sK4))
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f316])).

fof(f336,plain,
    ( ~ spl8_20
    | spl8_9
    | spl8_18 ),
    inference(avatar_split_clause,[],[f324,f311,f155,f333])).

fof(f333,plain,
    ( spl8_20
  <=> m1_subset_1(sK5(k2_enumset1(sK1,sK2,sK3,sK4),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f155,plain,
    ( spl8_9
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f311,plain,
    ( spl8_18
  <=> r2_hidden(sK5(k2_enumset1(sK1,sK2,sK3,sK4),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f324,plain,
    ( ~ m1_subset_1(sK5(k2_enumset1(sK1,sK2,sK3,sK4),sK0),sK0)
    | spl8_9
    | spl8_18 ),
    inference(unit_resulting_resolution,[],[f157,f313,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f313,plain,
    ( ~ r2_hidden(sK5(k2_enumset1(sK1,sK2,sK3,sK4),sK0),sK0)
    | spl8_18 ),
    inference(avatar_component_clause,[],[f311])).

fof(f157,plain,
    ( ~ v1_xboole_0(sK0)
    | spl8_9 ),
    inference(avatar_component_clause,[],[f155])).

fof(f319,plain,
    ( spl8_19
    | spl8_17 ),
    inference(avatar_split_clause,[],[f300,f284,f316])).

fof(f284,plain,
    ( spl8_17
  <=> r1_tarski(k2_enumset1(sK1,sK2,sK3,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f300,plain,
    ( r2_hidden(sK5(k2_enumset1(sK1,sK2,sK3,sK4),sK0),k2_enumset1(sK1,sK2,sK3,sK4))
    | spl8_17 ),
    inference(unit_resulting_resolution,[],[f286,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f23,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f286,plain,
    ( ~ r1_tarski(k2_enumset1(sK1,sK2,sK3,sK4),sK0)
    | spl8_17 ),
    inference(avatar_component_clause,[],[f284])).

fof(f314,plain,
    ( ~ spl8_18
    | spl8_17 ),
    inference(avatar_split_clause,[],[f301,f284,f311])).

fof(f301,plain,
    ( ~ r2_hidden(sK5(k2_enumset1(sK1,sK2,sK3,sK4),sK0),sK0)
    | spl8_17 ),
    inference(unit_resulting_resolution,[],[f286,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f288,plain,
    ( ~ spl8_17
    | spl8_14 ),
    inference(avatar_split_clause,[],[f273,f218,f284])).

fof(f218,plain,
    ( spl8_14
  <=> r2_hidden(k2_enumset1(sK1,sK2,sK3,sK4),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f273,plain,
    ( ~ r1_tarski(k2_enumset1(sK1,sK2,sK3,sK4),sK0)
    | spl8_14 ),
    inference(resolution,[],[f220,f64])).

fof(f64,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK6(X0,X1),X0)
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( r1_tarski(sK6(X0,X1),X0)
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f27,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK6(X0,X1),X0)
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( r1_tarski(sK6(X0,X1),X0)
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f220,plain,
    ( ~ r2_hidden(k2_enumset1(sK1,sK2,sK3,sK4),k1_zfmisc_1(sK0))
    | spl8_14 ),
    inference(avatar_component_clause,[],[f218])).

fof(f221,plain,
    ( ~ spl8_14
    | spl8_1 ),
    inference(avatar_split_clause,[],[f216,f76,f218])).

fof(f76,plain,
    ( spl8_1
  <=> m1_subset_1(k2_enumset1(sK1,sK2,sK3,sK4),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f216,plain,
    ( ~ r2_hidden(k2_enumset1(sK1,sK2,sK3,sK4),k1_zfmisc_1(sK0))
    | spl8_1 ),
    inference(subsumption_resolution,[],[f207,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(f207,plain,
    ( ~ r2_hidden(k2_enumset1(sK1,sK2,sK3,sK4),k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | spl8_1 ),
    inference(resolution,[],[f78,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f78,plain,
    ( ~ m1_subset_1(k2_enumset1(sK1,sK2,sK3,sK4),k1_zfmisc_1(sK0))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f76])).

fof(f158,plain,
    ( ~ spl8_9
    | spl8_2 ),
    inference(avatar_split_clause,[],[f105,f81,f155])).

fof(f81,plain,
    ( spl8_2
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f105,plain,
    ( ~ v1_xboole_0(sK0)
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f83,f41])).

fof(f41,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(f83,plain,
    ( k1_xboole_0 != sK0
    | spl8_2 ),
    inference(avatar_component_clause,[],[f81])).

fof(f104,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f35,f101])).

fof(f101,plain,
    ( spl8_6
  <=> m1_subset_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f35,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ~ m1_subset_1(k2_enumset1(sK1,sK2,sK3,sK4),k1_zfmisc_1(sK0))
    & k1_xboole_0 != sK0
    & m1_subset_1(sK4,sK0)
    & m1_subset_1(sK3,sK0)
    & m1_subset_1(sK2,sK0)
    & m1_subset_1(sK1,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f10,f19,f18,f17,f16])).

fof(f16,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ~ m1_subset_1(k2_enumset1(X1,X2,X3,X4),k1_zfmisc_1(X0))
                    & k1_xboole_0 != X0
                    & m1_subset_1(X4,X0) )
                & m1_subset_1(X3,X0) )
            & m1_subset_1(X2,X0) )
        & m1_subset_1(X1,X0) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ~ m1_subset_1(k2_enumset1(sK1,X2,X3,X4),k1_zfmisc_1(sK0))
                  & k1_xboole_0 != sK0
                  & m1_subset_1(X4,sK0) )
              & m1_subset_1(X3,sK0) )
          & m1_subset_1(X2,sK0) )
      & m1_subset_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ~ m1_subset_1(k2_enumset1(sK1,X2,X3,X4),k1_zfmisc_1(sK0))
                & k1_xboole_0 != sK0
                & m1_subset_1(X4,sK0) )
            & m1_subset_1(X3,sK0) )
        & m1_subset_1(X2,sK0) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ~ m1_subset_1(k2_enumset1(sK1,sK2,X3,X4),k1_zfmisc_1(sK0))
              & k1_xboole_0 != sK0
              & m1_subset_1(X4,sK0) )
          & m1_subset_1(X3,sK0) )
      & m1_subset_1(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ~ m1_subset_1(k2_enumset1(sK1,sK2,X3,X4),k1_zfmisc_1(sK0))
            & k1_xboole_0 != sK0
            & m1_subset_1(X4,sK0) )
        & m1_subset_1(X3,sK0) )
   => ( ? [X4] :
          ( ~ m1_subset_1(k2_enumset1(sK1,sK2,sK3,X4),k1_zfmisc_1(sK0))
          & k1_xboole_0 != sK0
          & m1_subset_1(X4,sK0) )
      & m1_subset_1(sK3,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X4] :
        ( ~ m1_subset_1(k2_enumset1(sK1,sK2,sK3,X4),k1_zfmisc_1(sK0))
        & k1_xboole_0 != sK0
        & m1_subset_1(X4,sK0) )
   => ( ~ m1_subset_1(k2_enumset1(sK1,sK2,sK3,sK4),k1_zfmisc_1(sK0))
      & k1_xboole_0 != sK0
      & m1_subset_1(sK4,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ~ m1_subset_1(k2_enumset1(X1,X2,X3,X4),k1_zfmisc_1(X0))
                  & k1_xboole_0 != X0
                  & m1_subset_1(X4,X0) )
              & m1_subset_1(X3,X0) )
          & m1_subset_1(X2,X0) )
      & m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ~ m1_subset_1(k2_enumset1(X1,X2,X3,X4),k1_zfmisc_1(X0))
                  & k1_xboole_0 != X0
                  & m1_subset_1(X4,X0) )
              & m1_subset_1(X3,X0) )
          & m1_subset_1(X2,X0) )
      & m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,X0)
       => ! [X2] :
            ( m1_subset_1(X2,X0)
           => ! [X3] :
                ( m1_subset_1(X3,X0)
               => ! [X4] :
                    ( m1_subset_1(X4,X0)
                   => ( k1_xboole_0 != X0
                     => m1_subset_1(k2_enumset1(X1,X2,X3,X4),k1_zfmisc_1(X0)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ! [X2] :
          ( m1_subset_1(X2,X0)
         => ! [X3] :
              ( m1_subset_1(X3,X0)
             => ! [X4] :
                  ( m1_subset_1(X4,X0)
                 => ( k1_xboole_0 != X0
                   => m1_subset_1(k2_enumset1(X1,X2,X3,X4),k1_zfmisc_1(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_subset_1)).

fof(f99,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f36,f96])).

fof(f96,plain,
    ( spl8_5
  <=> m1_subset_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f36,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f94,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f37,f91])).

fof(f91,plain,
    ( spl8_4
  <=> m1_subset_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f37,plain,(
    m1_subset_1(sK3,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f89,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f38,f86])).

fof(f86,plain,
    ( spl8_3
  <=> m1_subset_1(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f38,plain,(
    m1_subset_1(sK4,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f84,plain,(
    ~ spl8_2 ),
    inference(avatar_split_clause,[],[f39,f81])).

fof(f39,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f20])).

fof(f79,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f40,f76])).

fof(f40,plain,(
    ~ m1_subset_1(k2_enumset1(sK1,sK2,sK3,sK4),k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f20])).

%------------------------------------------------------------------------------
