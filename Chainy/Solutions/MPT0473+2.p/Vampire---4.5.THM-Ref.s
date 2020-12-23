%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0473+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:32 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   43 (  73 expanded)
%              Number of leaves         :   12 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :  119 ( 225 expanded)
%              Number of equality atoms :   68 ( 138 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f947,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f876,f879,f883,f887,f891,f938,f944,f945,f946])).

fof(f946,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 = k2_relat_1(sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f945,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 = k1_relat_1(sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f944,plain,
    ( spl13_11
    | ~ spl13_1
    | ~ spl13_3 ),
    inference(avatar_split_clause,[],[f943,f881,f871,f936])).

fof(f936,plain,
    ( spl13_11
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_11])])).

fof(f871,plain,
    ( spl13_1
  <=> k1_xboole_0 = k1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).

fof(f881,plain,
    ( spl13_3
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_3])])).

fof(f943,plain,
    ( k1_xboole_0 = sK0
    | ~ spl13_1
    | ~ spl13_3 ),
    inference(subsumption_resolution,[],[f942,f882])).

fof(f882,plain,
    ( v1_relat_1(sK0)
    | ~ spl13_3 ),
    inference(avatar_component_clause,[],[f881])).

fof(f942,plain,
    ( k1_xboole_0 = sK0
    | ~ v1_relat_1(sK0)
    | ~ spl13_1 ),
    inference(trivial_inequality_removal,[],[f939])).

fof(f939,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | ~ v1_relat_1(sK0)
    | ~ spl13_1 ),
    inference(superposition,[],[f805,f877])).

fof(f877,plain,
    ( k1_xboole_0 = k1_relat_1(sK0)
    | ~ spl13_1 ),
    inference(avatar_component_clause,[],[f871])).

fof(f805,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f728])).

fof(f728,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f727])).

fof(f727,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f706])).

fof(f706,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f938,plain,
    ( spl13_11
    | ~ spl13_2
    | ~ spl13_3 ),
    inference(avatar_split_clause,[],[f934,f881,f874,f936])).

fof(f874,plain,
    ( spl13_2
  <=> k1_xboole_0 = k2_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).

fof(f934,plain,
    ( k1_xboole_0 = sK0
    | ~ spl13_2
    | ~ spl13_3 ),
    inference(subsumption_resolution,[],[f933,f882])).

fof(f933,plain,
    ( k1_xboole_0 = sK0
    | ~ v1_relat_1(sK0)
    | ~ spl13_2 ),
    inference(trivial_inequality_removal,[],[f931])).

fof(f931,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | ~ v1_relat_1(sK0)
    | ~ spl13_2 ),
    inference(superposition,[],[f806,f878])).

fof(f878,plain,
    ( k1_xboole_0 = k2_relat_1(sK0)
    | ~ spl13_2 ),
    inference(avatar_component_clause,[],[f874])).

fof(f806,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f728])).

fof(f891,plain,(
    spl13_5 ),
    inference(avatar_split_clause,[],[f809,f889])).

fof(f889,plain,
    ( spl13_5
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_5])])).

fof(f809,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f703])).

fof(f703,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f887,plain,(
    spl13_4 ),
    inference(avatar_split_clause,[],[f810,f885])).

fof(f885,plain,
    ( spl13_4
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_4])])).

fof(f810,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f703])).

fof(f883,plain,(
    spl13_3 ),
    inference(avatar_split_clause,[],[f784,f881])).

fof(f784,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f755])).

fof(f755,plain,
    ( ( k1_xboole_0 != k2_relat_1(sK0)
      | k1_xboole_0 != k1_relat_1(sK0) )
    & ( k1_xboole_0 = k2_relat_1(sK0)
      | k1_xboole_0 = k1_relat_1(sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f753,f754])).

fof(f754,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k2_relat_1(sK0)
        | k1_xboole_0 != k1_relat_1(sK0) )
      & ( k1_xboole_0 = k2_relat_1(sK0)
        | k1_xboole_0 = k1_relat_1(sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f753,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k2_relat_1(X0)
        | k1_xboole_0 != k1_relat_1(X0) )
      & ( k1_xboole_0 = k2_relat_1(X0)
        | k1_xboole_0 = k1_relat_1(X0) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f752])).

fof(f752,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k2_relat_1(X0)
        | k1_xboole_0 != k1_relat_1(X0) )
      & ( k1_xboole_0 = k2_relat_1(X0)
        | k1_xboole_0 = k1_relat_1(X0) )
      & v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f709])).

fof(f709,plain,(
    ? [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <~> k1_xboole_0 = k2_relat_1(X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f708])).

fof(f708,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k1_relat_1(X0)
        <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    inference(negated_conjecture,[],[f707])).

fof(f707,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(f879,plain,
    ( spl13_1
    | spl13_2 ),
    inference(avatar_split_clause,[],[f785,f874,f871])).

fof(f785,plain,
    ( k1_xboole_0 = k2_relat_1(sK0)
    | k1_xboole_0 = k1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f755])).

fof(f876,plain,
    ( ~ spl13_1
    | ~ spl13_2 ),
    inference(avatar_split_clause,[],[f786,f874,f871])).

fof(f786,plain,
    ( k1_xboole_0 != k2_relat_1(sK0)
    | k1_xboole_0 != k1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f755])).
%------------------------------------------------------------------------------
