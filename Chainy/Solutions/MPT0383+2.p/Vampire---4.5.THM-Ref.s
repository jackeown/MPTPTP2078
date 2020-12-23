%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0383+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:27 EST 2020

% Result     : Theorem 6.73s
% Output     : Refutation 6.73s
% Verified   : 
% Statistics : Number of formulae       :   49 (  94 expanded)
%              Number of leaves         :   11 (  36 expanded)
%              Depth                    :   10
%              Number of atoms          :  160 ( 333 expanded)
%              Number of equality atoms :   17 (  40 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10150,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1583,f1593,f3034,f3075,f10109,f10147])).

fof(f10147,plain,
    ( ~ spl71_25
    | ~ spl71_26
    | ~ spl71_40 ),
    inference(avatar_contradiction_clause,[],[f10146])).

fof(f10146,plain,
    ( $false
    | ~ spl71_25
    | ~ spl71_26
    | ~ spl71_40 ),
    inference(subsumption_resolution,[],[f10145,f10061])).

fof(f10061,plain,
    ( m1_subset_1(sK8(sK0,sK1,sK3),sK0)
    | ~ spl71_25 ),
    inference(unit_resulting_resolution,[],[f3033,f1566])).

fof(f1566,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(subsumption_resolution,[],[f1238,f1229])).

fof(f1229,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f666])).

fof(f666,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f148])).

fof(f148,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(f1238,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f872])).

fof(f872,plain,(
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
    inference(nnf_transformation,[],[f676])).

fof(f676,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f456])).

fof(f456,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f3033,plain,
    ( r2_hidden(sK8(sK0,sK1,sK3),sK0)
    | ~ spl71_25 ),
    inference(avatar_component_clause,[],[f3031])).

fof(f3031,plain,
    ( spl71_25
  <=> r2_hidden(sK8(sK0,sK1,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl71_25])])).

fof(f10145,plain,
    ( ~ m1_subset_1(sK8(sK0,sK1,sK3),sK0)
    | ~ spl71_26
    | ~ spl71_40 ),
    inference(subsumption_resolution,[],[f10144,f10062])).

fof(f10062,plain,
    ( m1_subset_1(sK9(sK0,sK1,sK3),sK1)
    | ~ spl71_26 ),
    inference(unit_resulting_resolution,[],[f3074,f1566])).

fof(f3074,plain,
    ( r2_hidden(sK9(sK0,sK1,sK3),sK1)
    | ~ spl71_26 ),
    inference(avatar_component_clause,[],[f3072])).

fof(f3072,plain,
    ( spl71_26
  <=> r2_hidden(sK9(sK0,sK1,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl71_26])])).

fof(f10144,plain,
    ( ~ m1_subset_1(sK9(sK0,sK1,sK3),sK1)
    | ~ m1_subset_1(sK8(sK0,sK1,sK3),sK0)
    | ~ spl71_40 ),
    inference(trivial_inequality_removal,[],[f10110])).

fof(f10110,plain,
    ( sK3 != sK3
    | ~ m1_subset_1(sK9(sK0,sK1,sK3),sK1)
    | ~ m1_subset_1(sK8(sK0,sK1,sK3),sK0)
    | ~ spl71_40 ),
    inference(superposition,[],[f925,f10108])).

fof(f10108,plain,
    ( sK3 = k4_tarski(sK8(sK0,sK1,sK3),sK9(sK0,sK1,sK3))
    | ~ spl71_40 ),
    inference(avatar_component_clause,[],[f10106])).

fof(f10106,plain,
    ( spl71_40
  <=> sK3 = k4_tarski(sK8(sK0,sK1,sK3),sK9(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl71_40])])).

fof(f925,plain,(
    ! [X4,X5] :
      ( k4_tarski(X4,X5) != sK3
      | ~ m1_subset_1(X5,sK1)
      | ~ m1_subset_1(X4,sK0) ) ),
    inference(cnf_transformation,[],[f759])).

fof(f759,plain,
    ( ! [X4] :
        ( ! [X5] :
            ( k4_tarski(X4,X5) != sK3
            | ~ m1_subset_1(X5,sK1) )
        | ~ m1_subset_1(X4,sK0) )
    & r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
    & r2_hidden(sK3,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f546,f758])).

fof(f758,plain,
    ( ? [X0,X1,X2,X3] :
        ( ! [X4] :
            ( ! [X5] :
                ( k4_tarski(X4,X5) != X3
                | ~ m1_subset_1(X5,X1) )
            | ~ m1_subset_1(X4,X0) )
        & r1_tarski(X2,k2_zfmisc_1(X0,X1))
        & r2_hidden(X3,X2) )
   => ( ! [X4] :
          ( ! [X5] :
              ( k4_tarski(X4,X5) != sK3
              | ~ m1_subset_1(X5,sK1) )
          | ~ m1_subset_1(X4,sK0) )
      & r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
      & r2_hidden(sK3,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f546,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( k4_tarski(X4,X5) != X3
              | ~ m1_subset_1(X5,X1) )
          | ~ m1_subset_1(X4,X0) )
      & r1_tarski(X2,k2_zfmisc_1(X0,X1))
      & r2_hidden(X3,X2) ) ),
    inference(ennf_transformation,[],[f538])).

fof(f538,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( ! [X4] :
              ( m1_subset_1(X4,X0)
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => k4_tarski(X4,X5) != X3 ) )
          & r1_tarski(X2,k2_zfmisc_1(X0,X1))
          & r2_hidden(X3,X2) ) ),
    inference(negated_conjecture,[],[f537])).

fof(f537,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( ! [X4] :
            ( m1_subset_1(X4,X0)
           => ! [X5] :
                ( m1_subset_1(X5,X1)
               => k4_tarski(X4,X5) != X3 ) )
        & r1_tarski(X2,k2_zfmisc_1(X0,X1))
        & r2_hidden(X3,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_subset_1)).

fof(f10109,plain,
    ( spl71_40
    | ~ spl71_1
    | ~ spl71_3 ),
    inference(avatar_split_clause,[],[f2538,f1590,f1580,f10106])).

fof(f1580,plain,
    ( spl71_1
  <=> r2_hidden(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl71_1])])).

fof(f1590,plain,
    ( spl71_3
  <=> r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl71_3])])).

fof(f2538,plain,
    ( sK3 = k4_tarski(sK8(sK0,sK1,sK3),sK9(sK0,sK1,sK3))
    | ~ spl71_1
    | ~ spl71_3 ),
    inference(unit_resulting_resolution,[],[f1582,f1592,f933])).

fof(f933,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | ~ r2_hidden(X3,X0)
      | k4_tarski(sK8(X1,X2,X3),sK9(X1,X2,X3)) = X3 ) ),
    inference(cnf_transformation,[],[f766])).

fof(f766,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k4_tarski(sK8(X1,X2,X3),sK9(X1,X2,X3)) = X3
        & r2_hidden(sK9(X1,X2,X3),X2)
        & r2_hidden(sK8(X1,X2,X3),X1) )
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f550,f765])).

fof(f765,plain,(
    ! [X3,X2,X1] :
      ( ? [X4,X5] :
          ( k4_tarski(X4,X5) = X3
          & r2_hidden(X5,X2)
          & r2_hidden(X4,X1) )
     => ( k4_tarski(sK8(X1,X2,X3),sK9(X1,X2,X3)) = X3
        & r2_hidden(sK9(X1,X2,X3),X2)
        & r2_hidden(sK8(X1,X2,X3),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f550,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4,X5] :
          ( k4_tarski(X4,X5) = X3
          & r2_hidden(X5,X2)
          & r2_hidden(X4,X1) )
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f322])).

fof(f322,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ! [X4,X5] :
            ~ ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X2)
              & r2_hidden(X4,X1) )
        & r2_hidden(X3,X0)
        & r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_zfmisc_1)).

fof(f1592,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ spl71_3 ),
    inference(avatar_component_clause,[],[f1590])).

fof(f1582,plain,
    ( r2_hidden(sK3,sK2)
    | ~ spl71_1 ),
    inference(avatar_component_clause,[],[f1580])).

fof(f3075,plain,
    ( spl71_26
    | ~ spl71_1
    | ~ spl71_3 ),
    inference(avatar_split_clause,[],[f2229,f1590,f1580,f3072])).

fof(f2229,plain,
    ( r2_hidden(sK9(sK0,sK1,sK3),sK1)
    | ~ spl71_1
    | ~ spl71_3 ),
    inference(unit_resulting_resolution,[],[f1582,f1592,f932])).

fof(f932,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | ~ r2_hidden(X3,X0)
      | r2_hidden(sK9(X1,X2,X3),X2) ) ),
    inference(cnf_transformation,[],[f766])).

fof(f3034,plain,
    ( spl71_25
    | ~ spl71_1
    | ~ spl71_3 ),
    inference(avatar_split_clause,[],[f2222,f1590,f1580,f3031])).

fof(f2222,plain,
    ( r2_hidden(sK8(sK0,sK1,sK3),sK0)
    | ~ spl71_1
    | ~ spl71_3 ),
    inference(unit_resulting_resolution,[],[f1582,f1592,f931])).

fof(f931,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | ~ r2_hidden(X3,X0)
      | r2_hidden(sK8(X1,X2,X3),X1) ) ),
    inference(cnf_transformation,[],[f766])).

fof(f1593,plain,(
    spl71_3 ),
    inference(avatar_split_clause,[],[f924,f1590])).

fof(f924,plain,(
    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f759])).

fof(f1583,plain,(
    spl71_1 ),
    inference(avatar_split_clause,[],[f923,f1580])).

fof(f923,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f759])).
%------------------------------------------------------------------------------
