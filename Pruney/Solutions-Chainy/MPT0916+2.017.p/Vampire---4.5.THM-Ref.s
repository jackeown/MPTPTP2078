%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 288 expanded)
%              Number of leaves         :   46 ( 140 expanded)
%              Depth                    :    8
%              Number of atoms          :  407 (1127 expanded)
%              Number of equality atoms :   59 ( 106 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f421,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f58,f63,f68,f73,f91,f96,f101,f113,f127,f133,f166,f172,f184,f190,f221,f237,f242,f257,f399,f400,f401,f402,f410,f417,f418,f419,f420])).

fof(f420,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK6) != k2_mcart_1(sK6)
    | r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)
    | ~ r2_hidden(k2_mcart_1(sK6),sK5) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f419,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK6) != k2_mcart_1(k1_mcart_1(sK6))
    | r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)
    | ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f418,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK6) != k1_mcart_1(k1_mcart_1(sK6))
    | r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)
    | ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f417,plain,
    ( spl8_50
    | ~ spl8_5
    | spl8_45
    | spl8_46
    | spl8_47 ),
    inference(avatar_split_clause,[],[f411,f392,f388,f384,f70,f414])).

fof(f414,plain,
    ( spl8_50
  <=> k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_50])])).

fof(f70,plain,
    ( spl8_5
  <=> m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f384,plain,
    ( spl8_45
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_45])])).

fof(f388,plain,
    ( spl8_46
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_46])])).

fof(f392,plain,
    ( spl8_47
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_47])])).

fof(f411,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6))
    | ~ spl8_5
    | spl8_45
    | spl8_46
    | spl8_47 ),
    inference(unit_resulting_resolution,[],[f385,f389,f393,f72,f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f41,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
                & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
                & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).

fof(f72,plain,
    ( m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f70])).

fof(f393,plain,
    ( k1_xboole_0 != sK2
    | spl8_47 ),
    inference(avatar_component_clause,[],[f392])).

fof(f389,plain,
    ( k1_xboole_0 != sK1
    | spl8_46 ),
    inference(avatar_component_clause,[],[f388])).

fof(f385,plain,
    ( k1_xboole_0 != sK0
    | spl8_45 ),
    inference(avatar_component_clause,[],[f384])).

fof(f410,plain,
    ( spl8_49
    | ~ spl8_5
    | spl8_45
    | spl8_46
    | spl8_47 ),
    inference(avatar_split_clause,[],[f404,f392,f388,f384,f70,f407])).

fof(f407,plain,
    ( spl8_49
  <=> k6_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(k1_mcart_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_49])])).

fof(f404,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(k1_mcart_1(sK6))
    | ~ spl8_5
    | spl8_45
    | spl8_46
    | spl8_47 ),
    inference(unit_resulting_resolution,[],[f385,f389,f393,f72,f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f42,f37])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f402,plain,
    ( k1_xboole_0 != sK2
    | r1_tarski(sK5,k1_xboole_0)
    | ~ r1_tarski(sK5,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f401,plain,
    ( k1_xboole_0 != sK1
    | r1_tarski(sK4,k1_xboole_0)
    | ~ r1_tarski(sK4,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f400,plain,
    ( k1_xboole_0 != sK0
    | r1_tarski(sK3,k1_xboole_0)
    | ~ r1_tarski(sK3,sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f399,plain,
    ( spl8_45
    | spl8_46
    | spl8_47
    | spl8_48
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f382,f70,f396,f392,f388,f384])).

fof(f396,plain,
    ( spl8_48
  <=> k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_48])])).

fof(f382,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl8_5 ),
    inference(resolution,[],[f46,f72])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f43,f37])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f257,plain,
    ( ~ spl8_30
    | ~ spl8_31
    | ~ spl8_32 ),
    inference(avatar_split_clause,[],[f31,f254,f250,f246])).

fof(f246,plain,
    ( spl8_30
  <=> r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f250,plain,
    ( spl8_31
  <=> r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).

fof(f254,plain,
    ( spl8_32
  <=> r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f31,plain,
    ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)
    | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)
    | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)
      | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)
      | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) )
    & r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5))
    & m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2))
    & m1_subset_1(sK5,k1_zfmisc_1(sK2))
    & m1_subset_1(sK4,k1_zfmisc_1(sK1))
    & m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f11,f19,f18,f17,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                      | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                      | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
                    & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                    & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
                & m1_subset_1(X5,k1_zfmisc_1(X2)) )
            & m1_subset_1(X4,k1_zfmisc_1(X1)) )
        & m1_subset_1(X3,k1_zfmisc_1(X0)) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),X5)
                    | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),X4)
                    | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3) )
                  & r2_hidden(X6,k3_zfmisc_1(sK3,X4,X5))
                  & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2)) )
              & m1_subset_1(X5,k1_zfmisc_1(sK2)) )
          & m1_subset_1(X4,k1_zfmisc_1(sK1)) )
      & m1_subset_1(sK3,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),X5)
                  | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),X4)
                  | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3) )
                & r2_hidden(X6,k3_zfmisc_1(sK3,X4,X5))
                & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2)) )
            & m1_subset_1(X5,k1_zfmisc_1(sK2)) )
        & m1_subset_1(X4,k1_zfmisc_1(sK1)) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),X5)
                | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),sK4)
                | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3) )
              & r2_hidden(X6,k3_zfmisc_1(sK3,sK4,X5))
              & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2)) )
          & m1_subset_1(X5,k1_zfmisc_1(sK2)) )
      & m1_subset_1(sK4,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X5] :
        ( ? [X6] :
            ( ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),X5)
              | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),sK4)
              | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3) )
            & r2_hidden(X6,k3_zfmisc_1(sK3,sK4,X5))
            & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2)) )
        & m1_subset_1(X5,k1_zfmisc_1(sK2)) )
   => ( ? [X6] :
          ( ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),sK5)
            | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),sK4)
            | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3) )
          & r2_hidden(X6,k3_zfmisc_1(sK3,sK4,sK5))
          & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2)) )
      & m1_subset_1(sK5,k1_zfmisc_1(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X6] :
        ( ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),sK5)
          | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),sK4)
          | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3) )
        & r2_hidden(X6,k3_zfmisc_1(sK3,sK4,sK5))
        & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2)) )
   => ( ( ~ r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)
        | ~ r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)
        | ~ r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) )
      & r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5))
      & m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                    | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                    | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
                  & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                  & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
              & m1_subset_1(X5,k1_zfmisc_1(X2)) )
          & m1_subset_1(X4,k1_zfmisc_1(X1)) )
      & m1_subset_1(X3,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                    | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                    | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
                  & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                  & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
              & m1_subset_1(X5,k1_zfmisc_1(X2)) )
          & m1_subset_1(X4,k1_zfmisc_1(X1)) )
      & m1_subset_1(X3,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(X0))
       => ! [X4] :
            ( m1_subset_1(X4,k1_zfmisc_1(X1))
           => ! [X5] :
                ( m1_subset_1(X5,k1_zfmisc_1(X2))
               => ! [X6] :
                    ( m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))
                   => ( r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                     => ( r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                        & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                        & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X0))
     => ! [X4] :
          ( m1_subset_1(X4,k1_zfmisc_1(X1))
         => ! [X5] :
              ( m1_subset_1(X5,k1_zfmisc_1(X2))
             => ! [X6] :
                  ( m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))
                 => ( r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                   => ( r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                      & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                      & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_mcart_1)).

fof(f242,plain,
    ( ~ spl8_29
    | ~ spl8_8
    | spl8_21 ),
    inference(avatar_split_clause,[],[f208,f187,f93,f239])).

fof(f239,plain,
    ( spl8_29
  <=> r1_tarski(sK4,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).

fof(f93,plain,
    ( spl8_8
  <=> r1_tarski(sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f187,plain,
    ( spl8_21
  <=> v1_xboole_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f208,plain,
    ( ~ r1_tarski(sK4,k1_xboole_0)
    | ~ spl8_8
    | spl8_21 ),
    inference(unit_resulting_resolution,[],[f189,f95,f32,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X2,X0)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X2,X0)
      | v1_xboole_0(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X2,X0)
      | v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_xboole_0(X0,X1)
          & r1_tarski(X2,X1)
          & r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_xboole_1)).

fof(f32,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f95,plain,
    ( r1_tarski(sK4,sK1)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f93])).

fof(f189,plain,
    ( ~ v1_xboole_0(sK4)
    | spl8_21 ),
    inference(avatar_component_clause,[],[f187])).

fof(f237,plain,
    ( ~ spl8_28
    | ~ spl8_7
    | spl8_13 ),
    inference(avatar_split_clause,[],[f207,f130,f88,f234])).

fof(f234,plain,
    ( spl8_28
  <=> r1_tarski(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f88,plain,
    ( spl8_7
  <=> r1_tarski(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f130,plain,
    ( spl8_13
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f207,plain,
    ( ~ r1_tarski(sK3,k1_xboole_0)
    | ~ spl8_7
    | spl8_13 ),
    inference(unit_resulting_resolution,[],[f132,f90,f32,f38])).

fof(f90,plain,
    ( r1_tarski(sK3,sK0)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f88])).

fof(f132,plain,
    ( ~ v1_xboole_0(sK3)
    | spl8_13 ),
    inference(avatar_component_clause,[],[f130])).

fof(f221,plain,
    ( ~ spl8_25
    | ~ spl8_9
    | spl8_18 ),
    inference(avatar_split_clause,[],[f209,f169,f98,f218])).

fof(f218,plain,
    ( spl8_25
  <=> r1_tarski(sK5,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f98,plain,
    ( spl8_9
  <=> r1_tarski(sK5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f169,plain,
    ( spl8_18
  <=> v1_xboole_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f209,plain,
    ( ~ r1_tarski(sK5,k1_xboole_0)
    | ~ spl8_9
    | spl8_18 ),
    inference(unit_resulting_resolution,[],[f171,f100,f32,f38])).

fof(f100,plain,
    ( r1_tarski(sK5,sK2)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f98])).

fof(f171,plain,
    ( ~ v1_xboole_0(sK5)
    | spl8_18 ),
    inference(avatar_component_clause,[],[f169])).

fof(f190,plain,
    ( ~ spl8_21
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f185,f181,f187])).

fof(f181,plain,
    ( spl8_20
  <=> r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f185,plain,
    ( ~ v1_xboole_0(sK4)
    | ~ spl8_20 ),
    inference(unit_resulting_resolution,[],[f183,f33])).

fof(f33,plain,(
    ! [X2,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK7(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f22,f23])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK7(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f183,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4)
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f181])).

fof(f184,plain,
    ( spl8_20
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f156,f110,f181])).

fof(f110,plain,
    ( spl8_10
  <=> r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f156,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4)
    | ~ spl8_10 ),
    inference(unit_resulting_resolution,[],[f112,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f112,plain,
    ( r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,sK4))
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f110])).

fof(f172,plain,
    ( ~ spl8_18
    | ~ spl8_17 ),
    inference(avatar_split_clause,[],[f167,f163,f169])).

fof(f163,plain,
    ( spl8_17
  <=> r2_hidden(k2_mcart_1(sK6),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f167,plain,
    ( ~ v1_xboole_0(sK5)
    | ~ spl8_17 ),
    inference(unit_resulting_resolution,[],[f165,f33])).

fof(f165,plain,
    ( r2_hidden(k2_mcart_1(sK6),sK5)
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f163])).

fof(f166,plain,
    ( spl8_17
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f155,f65,f163])).

fof(f65,plain,
    ( spl8_4
  <=> r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f155,plain,
    ( r2_hidden(k2_mcart_1(sK6),sK5)
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f67,f40])).

fof(f67,plain,
    ( r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f65])).

fof(f133,plain,
    ( ~ spl8_13
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f128,f124,f130])).

fof(f124,plain,
    ( spl8_12
  <=> r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f128,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ spl8_12 ),
    inference(unit_resulting_resolution,[],[f126,f33])).

fof(f126,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f124])).

fof(f127,plain,
    ( spl8_12
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f114,f110,f124])).

fof(f114,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3)
    | ~ spl8_10 ),
    inference(unit_resulting_resolution,[],[f112,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f113,plain,
    ( spl8_10
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f106,f65,f110])).

fof(f106,plain,
    ( r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,sK4))
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f67,f39])).

fof(f101,plain,
    ( spl8_9
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f83,f60,f98])).

fof(f60,plain,
    ( spl8_3
  <=> m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f83,plain,
    ( r1_tarski(sK5,sK2)
    | ~ spl8_3 ),
    inference(unit_resulting_resolution,[],[f62,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f62,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2))
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f96,plain,
    ( spl8_8
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f82,f55,f93])).

fof(f55,plain,
    ( spl8_2
  <=> m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f82,plain,
    ( r1_tarski(sK4,sK1)
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f57,f35])).

fof(f57,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK1))
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f91,plain,
    ( spl8_7
    | ~ spl8_1 ),
    inference(avatar_split_clause,[],[f81,f50,f88])).

fof(f50,plain,
    ( spl8_1
  <=> m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f81,plain,
    ( r1_tarski(sK3,sK0)
    | ~ spl8_1 ),
    inference(unit_resulting_resolution,[],[f52,f35])).

fof(f52,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f73,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f45,f70])).

fof(f45,plain,(
    m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f29,f37])).

fof(f29,plain,(
    m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f20])).

fof(f68,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f44,f65])).

fof(f44,plain,(
    r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(definition_unfolding,[],[f30,f37])).

fof(f30,plain,(
    r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f20])).

fof(f63,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f28,f60])).

fof(f28,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f20])).

fof(f58,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f27,f55])).

fof(f27,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f53,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f26,f50])).

fof(f26,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:16:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.42  % (19638)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.43  % (19638)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f421,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(avatar_sat_refutation,[],[f53,f58,f63,f68,f73,f91,f96,f101,f113,f127,f133,f166,f172,f184,f190,f221,f237,f242,f257,f399,f400,f401,f402,f410,f417,f418,f419,f420])).
% 0.21/0.43  fof(f420,plain,(
% 0.21/0.43    k7_mcart_1(sK0,sK1,sK2,sK6) != k2_mcart_1(sK6) | r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) | ~r2_hidden(k2_mcart_1(sK6),sK5)),
% 0.21/0.43    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.43  fof(f419,plain,(
% 0.21/0.43    k6_mcart_1(sK0,sK1,sK2,sK6) != k2_mcart_1(k1_mcart_1(sK6)) | r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) | ~r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4)),
% 0.21/0.43    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.43  fof(f418,plain,(
% 0.21/0.43    k5_mcart_1(sK0,sK1,sK2,sK6) != k1_mcart_1(k1_mcart_1(sK6)) | r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3) | ~r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3)),
% 0.21/0.43    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.43  fof(f417,plain,(
% 0.21/0.43    spl8_50 | ~spl8_5 | spl8_45 | spl8_46 | spl8_47),
% 0.21/0.43    inference(avatar_split_clause,[],[f411,f392,f388,f384,f70,f414])).
% 0.21/0.43  fof(f414,plain,(
% 0.21/0.43    spl8_50 <=> k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl8_50])])).
% 0.21/0.43  fof(f70,plain,(
% 0.21/0.43    spl8_5 <=> m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.21/0.43  fof(f384,plain,(
% 0.21/0.43    spl8_45 <=> k1_xboole_0 = sK0),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl8_45])])).
% 0.21/0.43  fof(f388,plain,(
% 0.21/0.43    spl8_46 <=> k1_xboole_0 = sK1),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl8_46])])).
% 0.21/0.43  fof(f392,plain,(
% 0.21/0.43    spl8_47 <=> k1_xboole_0 = sK2),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl8_47])])).
% 0.21/0.43  fof(f411,plain,(
% 0.21/0.43    k5_mcart_1(sK0,sK1,sK2,sK6) = k1_mcart_1(k1_mcart_1(sK6)) | (~spl8_5 | spl8_45 | spl8_46 | spl8_47)),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f385,f389,f393,f72,f48])).
% 0.21/0.43  fof(f48,plain,(
% 0.21/0.43    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.43    inference(definition_unfolding,[],[f41,f37])).
% 0.21/0.43  fof(f37,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f5])).
% 0.21/0.43  fof(f5,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.21/0.43  fof(f41,plain,(
% 0.21/0.43    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.43    inference(cnf_transformation,[],[f15])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.43    inference(ennf_transformation,[],[f7])).
% 0.21/0.43  fof(f7,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).
% 0.21/0.43  fof(f72,plain,(
% 0.21/0.43    m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl8_5),
% 0.21/0.43    inference(avatar_component_clause,[],[f70])).
% 0.21/0.43  fof(f393,plain,(
% 0.21/0.43    k1_xboole_0 != sK2 | spl8_47),
% 0.21/0.43    inference(avatar_component_clause,[],[f392])).
% 0.21/0.43  fof(f389,plain,(
% 0.21/0.43    k1_xboole_0 != sK1 | spl8_46),
% 0.21/0.43    inference(avatar_component_clause,[],[f388])).
% 0.21/0.43  fof(f385,plain,(
% 0.21/0.43    k1_xboole_0 != sK0 | spl8_45),
% 0.21/0.43    inference(avatar_component_clause,[],[f384])).
% 0.21/0.43  fof(f410,plain,(
% 0.21/0.43    spl8_49 | ~spl8_5 | spl8_45 | spl8_46 | spl8_47),
% 0.21/0.43    inference(avatar_split_clause,[],[f404,f392,f388,f384,f70,f407])).
% 0.21/0.43  fof(f407,plain,(
% 0.21/0.43    spl8_49 <=> k6_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(k1_mcart_1(sK6))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl8_49])])).
% 0.21/0.43  fof(f404,plain,(
% 0.21/0.43    k6_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(k1_mcart_1(sK6)) | (~spl8_5 | spl8_45 | spl8_46 | spl8_47)),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f385,f389,f393,f72,f47])).
% 0.21/0.43  fof(f47,plain,(
% 0.21/0.43    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.43    inference(definition_unfolding,[],[f42,f37])).
% 0.21/0.43  fof(f42,plain,(
% 0.21/0.43    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.43    inference(cnf_transformation,[],[f15])).
% 0.21/0.43  fof(f402,plain,(
% 0.21/0.43    k1_xboole_0 != sK2 | r1_tarski(sK5,k1_xboole_0) | ~r1_tarski(sK5,sK2)),
% 0.21/0.43    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.43  fof(f401,plain,(
% 0.21/0.43    k1_xboole_0 != sK1 | r1_tarski(sK4,k1_xboole_0) | ~r1_tarski(sK4,sK1)),
% 0.21/0.43    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.43  fof(f400,plain,(
% 0.21/0.43    k1_xboole_0 != sK0 | r1_tarski(sK3,k1_xboole_0) | ~r1_tarski(sK3,sK0)),
% 0.21/0.43    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.43  fof(f399,plain,(
% 0.21/0.43    spl8_45 | spl8_46 | spl8_47 | spl8_48 | ~spl8_5),
% 0.21/0.43    inference(avatar_split_clause,[],[f382,f70,f396,f392,f388,f384])).
% 0.21/0.43  fof(f396,plain,(
% 0.21/0.43    spl8_48 <=> k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl8_48])])).
% 0.21/0.43  fof(f382,plain,(
% 0.21/0.43    k7_mcart_1(sK0,sK1,sK2,sK6) = k2_mcart_1(sK6) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl8_5),
% 0.21/0.43    inference(resolution,[],[f46,f72])).
% 0.21/0.43  fof(f46,plain,(
% 0.21/0.43    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.43    inference(definition_unfolding,[],[f43,f37])).
% 0.21/0.43  fof(f43,plain,(
% 0.21/0.43    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.43    inference(cnf_transformation,[],[f15])).
% 0.21/0.43  fof(f257,plain,(
% 0.21/0.43    ~spl8_30 | ~spl8_31 | ~spl8_32),
% 0.21/0.43    inference(avatar_split_clause,[],[f31,f254,f250,f246])).
% 0.21/0.43  fof(f246,plain,(
% 0.21/0.43    spl8_30 <=> r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).
% 0.21/0.43  fof(f250,plain,(
% 0.21/0.43    spl8_31 <=> r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).
% 0.21/0.43  fof(f254,plain,(
% 0.21/0.43    spl8_32 <=> r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).
% 0.21/0.43  fof(f31,plain,(
% 0.21/0.43    ~r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)),
% 0.21/0.43    inference(cnf_transformation,[],[f20])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    ((((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)) & r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5)) & m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2))) & m1_subset_1(sK5,k1_zfmisc_1(sK2))) & m1_subset_1(sK4,k1_zfmisc_1(sK1))) & m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f11,f19,f18,f17,f16])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) => (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),X5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),X4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3)) & r2_hidden(X6,k3_zfmisc_1(sK3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2))) & m1_subset_1(X5,k1_zfmisc_1(sK2))) & m1_subset_1(X4,k1_zfmisc_1(sK1))) & m1_subset_1(sK3,k1_zfmisc_1(sK0)))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    ? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),X5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),X4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3)) & r2_hidden(X6,k3_zfmisc_1(sK3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2))) & m1_subset_1(X5,k1_zfmisc_1(sK2))) & m1_subset_1(X4,k1_zfmisc_1(sK1))) => (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),X5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),sK4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3)) & r2_hidden(X6,k3_zfmisc_1(sK3,sK4,X5)) & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2))) & m1_subset_1(X5,k1_zfmisc_1(sK2))) & m1_subset_1(sK4,k1_zfmisc_1(sK1)))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    ? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),X5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),sK4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3)) & r2_hidden(X6,k3_zfmisc_1(sK3,sK4,X5)) & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2))) & m1_subset_1(X5,k1_zfmisc_1(sK2))) => (? [X6] : ((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),sK5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),sK4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3)) & r2_hidden(X6,k3_zfmisc_1(sK3,sK4,sK5)) & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2))) & m1_subset_1(sK5,k1_zfmisc_1(sK2)))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    ? [X6] : ((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,X6),sK5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,X6),sK4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,X6),sK3)) & r2_hidden(X6,k3_zfmisc_1(sK3,sK4,sK5)) & m1_subset_1(X6,k3_zfmisc_1(sK0,sK1,sK2))) => ((~r2_hidden(k7_mcart_1(sK0,sK1,sK2,sK6),sK5) | ~r2_hidden(k6_mcart_1(sK0,sK1,sK2,sK6),sK4) | ~r2_hidden(k5_mcart_1(sK0,sK1,sK2,sK6),sK3)) & r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5)) & m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2)))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0)))),
% 0.21/0.43    inference(flattening,[],[f10])).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : (((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f9])).
% 0.21/0.43  fof(f9,negated_conjecture,(
% 0.21/0.43    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X2)) => ! [X6] : (m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) => (r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) => (r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)))))))),
% 0.21/0.43    inference(negated_conjecture,[],[f8])).
% 0.21/0.43  fof(f8,conjecture,(
% 0.21/0.43    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X2)) => ! [X6] : (m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) => (r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) => (r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)))))))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_mcart_1)).
% 0.21/0.43  fof(f242,plain,(
% 0.21/0.43    ~spl8_29 | ~spl8_8 | spl8_21),
% 0.21/0.43    inference(avatar_split_clause,[],[f208,f187,f93,f239])).
% 0.21/0.43  fof(f239,plain,(
% 0.21/0.43    spl8_29 <=> r1_tarski(sK4,k1_xboole_0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).
% 0.21/0.43  fof(f93,plain,(
% 0.21/0.43    spl8_8 <=> r1_tarski(sK4,sK1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.21/0.43  fof(f187,plain,(
% 0.21/0.43    spl8_21 <=> v1_xboole_0(sK4)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).
% 0.21/0.43  fof(f208,plain,(
% 0.21/0.43    ~r1_tarski(sK4,k1_xboole_0) | (~spl8_8 | spl8_21)),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f189,f95,f32,f38])).
% 0.21/0.43  fof(f38,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X2,X0) | v1_xboole_0(X2)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f13])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (~r1_xboole_0(X0,X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X2,X0) | v1_xboole_0(X2))),
% 0.21/0.43    inference(flattening,[],[f12])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    ! [X0,X1,X2] : ((~r1_xboole_0(X0,X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X2,X0)) | v1_xboole_0(X2))),
% 0.21/0.43    inference(ennf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ~(r1_xboole_0(X0,X1) & r1_tarski(X2,X1) & r1_tarski(X2,X0)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_xboole_1)).
% 0.21/0.43  fof(f32,plain,(
% 0.21/0.43    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.43  fof(f95,plain,(
% 0.21/0.43    r1_tarski(sK4,sK1) | ~spl8_8),
% 0.21/0.43    inference(avatar_component_clause,[],[f93])).
% 0.21/0.43  fof(f189,plain,(
% 0.21/0.43    ~v1_xboole_0(sK4) | spl8_21),
% 0.21/0.43    inference(avatar_component_clause,[],[f187])).
% 0.21/0.43  fof(f237,plain,(
% 0.21/0.43    ~spl8_28 | ~spl8_7 | spl8_13),
% 0.21/0.43    inference(avatar_split_clause,[],[f207,f130,f88,f234])).
% 0.21/0.43  fof(f234,plain,(
% 0.21/0.43    spl8_28 <=> r1_tarski(sK3,k1_xboole_0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).
% 0.21/0.43  fof(f88,plain,(
% 0.21/0.43    spl8_7 <=> r1_tarski(sK3,sK0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.21/0.43  fof(f130,plain,(
% 0.21/0.43    spl8_13 <=> v1_xboole_0(sK3)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.21/0.43  fof(f207,plain,(
% 0.21/0.43    ~r1_tarski(sK3,k1_xboole_0) | (~spl8_7 | spl8_13)),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f132,f90,f32,f38])).
% 0.21/0.43  fof(f90,plain,(
% 0.21/0.43    r1_tarski(sK3,sK0) | ~spl8_7),
% 0.21/0.43    inference(avatar_component_clause,[],[f88])).
% 0.21/0.43  fof(f132,plain,(
% 0.21/0.43    ~v1_xboole_0(sK3) | spl8_13),
% 0.21/0.43    inference(avatar_component_clause,[],[f130])).
% 0.21/0.43  fof(f221,plain,(
% 0.21/0.43    ~spl8_25 | ~spl8_9 | spl8_18),
% 0.21/0.43    inference(avatar_split_clause,[],[f209,f169,f98,f218])).
% 0.21/0.43  fof(f218,plain,(
% 0.21/0.43    spl8_25 <=> r1_tarski(sK5,k1_xboole_0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).
% 0.21/0.43  fof(f98,plain,(
% 0.21/0.43    spl8_9 <=> r1_tarski(sK5,sK2)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.21/0.43  fof(f169,plain,(
% 0.21/0.43    spl8_18 <=> v1_xboole_0(sK5)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 0.21/0.43  fof(f209,plain,(
% 0.21/0.43    ~r1_tarski(sK5,k1_xboole_0) | (~spl8_9 | spl8_18)),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f171,f100,f32,f38])).
% 0.21/0.43  fof(f100,plain,(
% 0.21/0.43    r1_tarski(sK5,sK2) | ~spl8_9),
% 0.21/0.43    inference(avatar_component_clause,[],[f98])).
% 0.21/0.43  fof(f171,plain,(
% 0.21/0.43    ~v1_xboole_0(sK5) | spl8_18),
% 0.21/0.43    inference(avatar_component_clause,[],[f169])).
% 0.21/0.43  fof(f190,plain,(
% 0.21/0.43    ~spl8_21 | ~spl8_20),
% 0.21/0.43    inference(avatar_split_clause,[],[f185,f181,f187])).
% 0.21/0.43  fof(f181,plain,(
% 0.21/0.43    spl8_20 <=> r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 0.21/0.43  fof(f185,plain,(
% 0.21/0.43    ~v1_xboole_0(sK4) | ~spl8_20),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f183,f33])).
% 0.21/0.43  fof(f33,plain,(
% 0.21/0.43    ( ! [X2,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X2,X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f24])).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK7(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f22,f23])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK7(X0),X0))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.43    inference(rectify,[],[f21])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.43    inference(nnf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.43  fof(f183,plain,(
% 0.21/0.43    r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4) | ~spl8_20),
% 0.21/0.43    inference(avatar_component_clause,[],[f181])).
% 0.21/0.43  fof(f184,plain,(
% 0.21/0.43    spl8_20 | ~spl8_10),
% 0.21/0.43    inference(avatar_split_clause,[],[f156,f110,f181])).
% 0.21/0.43  fof(f110,plain,(
% 0.21/0.43    spl8_10 <=> r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,sK4))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.21/0.43  fof(f156,plain,(
% 0.21/0.43    r2_hidden(k2_mcart_1(k1_mcart_1(sK6)),sK4) | ~spl8_10),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f112,f40])).
% 0.21/0.43  fof(f40,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f14])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.43    inference(ennf_transformation,[],[f6])).
% 0.21/0.43  fof(f6,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.21/0.43  fof(f112,plain,(
% 0.21/0.43    r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,sK4)) | ~spl8_10),
% 0.21/0.43    inference(avatar_component_clause,[],[f110])).
% 0.21/0.43  fof(f172,plain,(
% 0.21/0.43    ~spl8_18 | ~spl8_17),
% 0.21/0.43    inference(avatar_split_clause,[],[f167,f163,f169])).
% 0.21/0.43  fof(f163,plain,(
% 0.21/0.43    spl8_17 <=> r2_hidden(k2_mcart_1(sK6),sK5)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 0.21/0.43  fof(f167,plain,(
% 0.21/0.43    ~v1_xboole_0(sK5) | ~spl8_17),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f165,f33])).
% 0.21/0.43  fof(f165,plain,(
% 0.21/0.43    r2_hidden(k2_mcart_1(sK6),sK5) | ~spl8_17),
% 0.21/0.43    inference(avatar_component_clause,[],[f163])).
% 0.21/0.43  fof(f166,plain,(
% 0.21/0.43    spl8_17 | ~spl8_4),
% 0.21/0.43    inference(avatar_split_clause,[],[f155,f65,f163])).
% 0.21/0.43  fof(f65,plain,(
% 0.21/0.43    spl8_4 <=> r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.43  fof(f155,plain,(
% 0.21/0.43    r2_hidden(k2_mcart_1(sK6),sK5) | ~spl8_4),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f67,f40])).
% 0.21/0.43  fof(f67,plain,(
% 0.21/0.43    r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) | ~spl8_4),
% 0.21/0.43    inference(avatar_component_clause,[],[f65])).
% 0.21/0.43  fof(f133,plain,(
% 0.21/0.43    ~spl8_13 | ~spl8_12),
% 0.21/0.43    inference(avatar_split_clause,[],[f128,f124,f130])).
% 0.21/0.43  fof(f124,plain,(
% 0.21/0.43    spl8_12 <=> r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.21/0.43  fof(f128,plain,(
% 0.21/0.43    ~v1_xboole_0(sK3) | ~spl8_12),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f126,f33])).
% 0.21/0.43  fof(f126,plain,(
% 0.21/0.43    r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3) | ~spl8_12),
% 0.21/0.43    inference(avatar_component_clause,[],[f124])).
% 0.21/0.43  fof(f127,plain,(
% 0.21/0.43    spl8_12 | ~spl8_10),
% 0.21/0.43    inference(avatar_split_clause,[],[f114,f110,f124])).
% 0.21/0.43  fof(f114,plain,(
% 0.21/0.43    r2_hidden(k1_mcart_1(k1_mcart_1(sK6)),sK3) | ~spl8_10),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f112,f39])).
% 0.21/0.43  fof(f39,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f14])).
% 0.21/0.43  fof(f113,plain,(
% 0.21/0.43    spl8_10 | ~spl8_4),
% 0.21/0.43    inference(avatar_split_clause,[],[f106,f65,f110])).
% 0.21/0.43  fof(f106,plain,(
% 0.21/0.43    r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK3,sK4)) | ~spl8_4),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f67,f39])).
% 0.21/0.43  fof(f101,plain,(
% 0.21/0.43    spl8_9 | ~spl8_3),
% 0.21/0.43    inference(avatar_split_clause,[],[f83,f60,f98])).
% 0.21/0.43  fof(f60,plain,(
% 0.21/0.43    spl8_3 <=> m1_subset_1(sK5,k1_zfmisc_1(sK2))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.43  fof(f83,plain,(
% 0.21/0.43    r1_tarski(sK5,sK2) | ~spl8_3),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f62,f35])).
% 0.21/0.43  fof(f35,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f25])).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.43    inference(nnf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,axiom,(
% 0.21/0.43    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.43  fof(f62,plain,(
% 0.21/0.43    m1_subset_1(sK5,k1_zfmisc_1(sK2)) | ~spl8_3),
% 0.21/0.43    inference(avatar_component_clause,[],[f60])).
% 0.21/0.43  fof(f96,plain,(
% 0.21/0.43    spl8_8 | ~spl8_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f82,f55,f93])).
% 0.21/0.43  fof(f55,plain,(
% 0.21/0.43    spl8_2 <=> m1_subset_1(sK4,k1_zfmisc_1(sK1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.43  fof(f82,plain,(
% 0.21/0.43    r1_tarski(sK4,sK1) | ~spl8_2),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f57,f35])).
% 0.21/0.43  fof(f57,plain,(
% 0.21/0.43    m1_subset_1(sK4,k1_zfmisc_1(sK1)) | ~spl8_2),
% 0.21/0.43    inference(avatar_component_clause,[],[f55])).
% 0.21/0.43  fof(f91,plain,(
% 0.21/0.43    spl8_7 | ~spl8_1),
% 0.21/0.43    inference(avatar_split_clause,[],[f81,f50,f88])).
% 0.21/0.43  fof(f50,plain,(
% 0.21/0.43    spl8_1 <=> m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.43  fof(f81,plain,(
% 0.21/0.43    r1_tarski(sK3,sK0) | ~spl8_1),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f52,f35])).
% 0.21/0.43  fof(f52,plain,(
% 0.21/0.43    m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~spl8_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f50])).
% 0.21/0.43  fof(f73,plain,(
% 0.21/0.43    spl8_5),
% 0.21/0.43    inference(avatar_split_clause,[],[f45,f70])).
% 0.21/0.43  fof(f45,plain,(
% 0.21/0.43    m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.21/0.43    inference(definition_unfolding,[],[f29,f37])).
% 0.21/0.43  fof(f29,plain,(
% 0.21/0.43    m1_subset_1(sK6,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.21/0.43    inference(cnf_transformation,[],[f20])).
% 0.21/0.43  fof(f68,plain,(
% 0.21/0.43    spl8_4),
% 0.21/0.43    inference(avatar_split_clause,[],[f44,f65])).
% 0.21/0.43  fof(f44,plain,(
% 0.21/0.43    r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 0.21/0.43    inference(definition_unfolding,[],[f30,f37])).
% 0.21/0.43  fof(f30,plain,(
% 0.21/0.43    r2_hidden(sK6,k3_zfmisc_1(sK3,sK4,sK5))),
% 0.21/0.43    inference(cnf_transformation,[],[f20])).
% 0.21/0.43  fof(f63,plain,(
% 0.21/0.43    spl8_3),
% 0.21/0.43    inference(avatar_split_clause,[],[f28,f60])).
% 0.21/0.43  fof(f28,plain,(
% 0.21/0.43    m1_subset_1(sK5,k1_zfmisc_1(sK2))),
% 0.21/0.43    inference(cnf_transformation,[],[f20])).
% 0.21/0.43  fof(f58,plain,(
% 0.21/0.43    spl8_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f27,f55])).
% 0.21/0.43  fof(f27,plain,(
% 0.21/0.43    m1_subset_1(sK4,k1_zfmisc_1(sK1))),
% 0.21/0.43    inference(cnf_transformation,[],[f20])).
% 0.21/0.43  fof(f53,plain,(
% 0.21/0.43    spl8_1),
% 0.21/0.43    inference(avatar_split_clause,[],[f26,f50])).
% 0.21/0.43  fof(f26,plain,(
% 0.21/0.43    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.21/0.43    inference(cnf_transformation,[],[f20])).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (19638)------------------------------
% 0.21/0.43  % (19638)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (19638)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (19638)Memory used [KB]: 11001
% 0.21/0.43  % (19638)Time elapsed: 0.014 s
% 0.21/0.43  % (19638)------------------------------
% 0.21/0.43  % (19638)------------------------------
% 0.21/0.43  % (19620)Success in time 0.079 s
%------------------------------------------------------------------------------
