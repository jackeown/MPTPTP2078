%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0537+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   31 (  43 expanded)
%              Number of leaves         :    9 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :   65 (  91 expanded)
%              Number of equality atoms :   12 (  20 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1972,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1497,f1502,f1536,f1564,f1970])).

fof(f1970,plain,
    ( spl35_12
    | ~ spl35_2
    | ~ spl35_8 ),
    inference(avatar_split_clause,[],[f1956,f1533,f1499,f1561])).

fof(f1561,plain,
    ( spl35_12
  <=> v1_xboole_0(k8_relat_1(k1_xboole_0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl35_12])])).

fof(f1499,plain,
    ( spl35_2
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl35_2])])).

fof(f1533,plain,
    ( spl35_8
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl35_8])])).

fof(f1956,plain,
    ( v1_xboole_0(k8_relat_1(k1_xboole_0,sK0))
    | ~ spl35_2
    | ~ spl35_8 ),
    inference(unit_resulting_resolution,[],[f1501,f1535,f1217])).

fof(f1217,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | v1_xboole_0(k8_relat_1(X1,X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f839])).

fof(f839,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(k8_relat_1(X1,X0))
        & v1_xboole_0(k8_relat_1(X1,X0)) )
      | ~ v1_xboole_0(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f838])).

fof(f838,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(k8_relat_1(X1,X0))
        & v1_xboole_0(k8_relat_1(X1,X0)) )
      | ~ v1_xboole_0(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f667])).

fof(f667,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & v1_relat_1(X0) )
     => ( v1_relat_1(k8_relat_1(X1,X0))
        & v1_xboole_0(k8_relat_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc18_relat_1)).

fof(f1535,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl35_8 ),
    inference(avatar_component_clause,[],[f1533])).

fof(f1501,plain,
    ( v1_relat_1(sK0)
    | ~ spl35_2 ),
    inference(avatar_component_clause,[],[f1499])).

fof(f1564,plain,
    ( ~ spl35_12
    | spl35_1 ),
    inference(avatar_split_clause,[],[f1558,f1494,f1561])).

fof(f1494,plain,
    ( spl35_1
  <=> k1_xboole_0 = k8_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl35_1])])).

fof(f1558,plain,
    ( ~ v1_xboole_0(k8_relat_1(k1_xboole_0,sK0))
    | spl35_1 ),
    inference(unit_resulting_resolution,[],[f1496,f1311])).

fof(f1311,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f895])).

fof(f895,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f136])).

fof(f136,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(f1496,plain,
    ( k1_xboole_0 != k8_relat_1(k1_xboole_0,sK0)
    | spl35_1 ),
    inference(avatar_component_clause,[],[f1494])).

fof(f1536,plain,(
    spl35_8 ),
    inference(avatar_split_clause,[],[f1337,f1533])).

fof(f1337,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f1502,plain,(
    spl35_2 ),
    inference(avatar_split_clause,[],[f1106,f1499])).

fof(f1106,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f996])).

fof(f996,plain,
    ( k1_xboole_0 != k8_relat_1(k1_xboole_0,sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f787,f995])).

fof(f995,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k8_relat_1(k1_xboole_0,X0)
        & v1_relat_1(X0) )
   => ( k1_xboole_0 != k8_relat_1(k1_xboole_0,sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f787,plain,(
    ? [X0] :
      ( k1_xboole_0 != k8_relat_1(k1_xboole_0,X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f714])).

fof(f714,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k1_xboole_0 = k8_relat_1(k1_xboole_0,X0) ) ),
    inference(negated_conjecture,[],[f713])).

fof(f713,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k8_relat_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_relat_1)).

fof(f1497,plain,(
    ~ spl35_1 ),
    inference(avatar_split_clause,[],[f1107,f1494])).

fof(f1107,plain,(
    k1_xboole_0 != k8_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f996])).
%------------------------------------------------------------------------------
