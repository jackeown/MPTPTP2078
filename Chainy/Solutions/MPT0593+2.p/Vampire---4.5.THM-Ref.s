%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0593+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.20s
% Verified   : 
% Statistics : Number of formulae       :   42 (  82 expanded)
%              Number of leaves         :   12 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :  120 ( 323 expanded)
%              Number of equality atoms :   59 ( 182 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1044,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f959,f963,f967,f971,f975,f1037,f1042,f1043])).

fof(f1043,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != sK1
    | sK0 = sK1 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1042,plain,
    ( spl7_14
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f1038,f969,f961,f1040])).

fof(f1040,plain,
    ( spl7_14
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f961,plain,
    ( spl7_2
  <=> k1_xboole_0 = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f969,plain,
    ( spl7_4
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f1038,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f1030,f970])).

fof(f970,plain,
    ( v1_relat_1(sK1)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f969])).

fof(f1030,plain,
    ( k1_xboole_0 = sK1
    | ~ v1_relat_1(sK1)
    | ~ spl7_2 ),
    inference(trivial_inequality_removal,[],[f1029])).

fof(f1029,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1
    | ~ v1_relat_1(sK1)
    | ~ spl7_2 ),
    inference(superposition,[],[f918,f962])).

fof(f962,plain,
    ( k1_xboole_0 = k2_relat_1(sK1)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f961])).

fof(f918,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f871])).

fof(f871,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f870])).

fof(f870,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f825])).

fof(f825,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f1037,plain,
    ( spl7_13
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f1033,f973,f965,f1035])).

fof(f1035,plain,
    ( spl7_13
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f965,plain,
    ( spl7_3
  <=> k1_xboole_0 = k2_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f973,plain,
    ( spl7_5
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f1033,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f1031,f974])).

fof(f974,plain,
    ( v1_relat_1(sK0)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f973])).

fof(f1031,plain,
    ( k1_xboole_0 = sK0
    | ~ v1_relat_1(sK0)
    | ~ spl7_3 ),
    inference(trivial_inequality_removal,[],[f1028])).

fof(f1028,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | ~ v1_relat_1(sK0)
    | ~ spl7_3 ),
    inference(superposition,[],[f918,f966])).

fof(f966,plain,
    ( k1_xboole_0 = k2_relat_1(sK0)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f965])).

fof(f975,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f899,f973])).

fof(f899,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f883])).

fof(f883,plain,
    ( sK0 != sK1
    & k1_xboole_0 = k2_relat_1(sK1)
    & k1_xboole_0 = k2_relat_1(sK0)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f856,f882,f881])).

fof(f881,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( X0 != X1
            & k1_xboole_0 = k2_relat_1(X1)
            & k1_xboole_0 = k2_relat_1(X0)
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( sK0 != X1
          & k1_xboole_0 = k2_relat_1(X1)
          & k1_xboole_0 = k2_relat_1(sK0)
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f882,plain,
    ( ? [X1] :
        ( sK0 != X1
        & k1_xboole_0 = k2_relat_1(X1)
        & k1_xboole_0 = k2_relat_1(sK0)
        & v1_relat_1(X1) )
   => ( sK0 != sK1
      & k1_xboole_0 = k2_relat_1(sK1)
      & k1_xboole_0 = k2_relat_1(sK0)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f856,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & k1_xboole_0 = k2_relat_1(X1)
          & k1_xboole_0 = k2_relat_1(X0)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f855])).

fof(f855,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & k1_xboole_0 = k2_relat_1(X1)
          & k1_xboole_0 = k2_relat_1(X0)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f788])).

fof(f788,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( ( k1_xboole_0 = k2_relat_1(X1)
                & k1_xboole_0 = k2_relat_1(X0) )
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f787])).

fof(f787,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( ( k1_xboole_0 = k2_relat_1(X1)
              & k1_xboole_0 = k2_relat_1(X0) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t197_relat_1)).

fof(f971,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f900,f969])).

fof(f900,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f883])).

fof(f967,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f901,f965])).

fof(f901,plain,(
    k1_xboole_0 = k2_relat_1(sK0) ),
    inference(cnf_transformation,[],[f883])).

fof(f963,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f902,f961])).

fof(f902,plain,(
    k1_xboole_0 = k2_relat_1(sK1) ),
    inference(cnf_transformation,[],[f883])).

fof(f959,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f903,f957])).

fof(f957,plain,
    ( spl7_1
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f903,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f883])).
%------------------------------------------------------------------------------
