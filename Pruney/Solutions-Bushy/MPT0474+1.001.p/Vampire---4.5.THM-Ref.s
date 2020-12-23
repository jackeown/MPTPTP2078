%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0474+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:03 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   32 (  39 expanded)
%              Number of leaves         :    9 (  16 expanded)
%              Depth                    :    5
%              Number of atoms          :   68 (  87 expanded)
%              Number of equality atoms :   15 (  19 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f46,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f18,f23,f27,f35,f41,f45])).

fof(f45,plain,
    ( spl0_1
    | ~ spl0_2
    | ~ spl0_6 ),
    inference(avatar_contradiction_clause,[],[f44])).

fof(f44,plain,
    ( $false
    | spl0_1
    | ~ spl0_2
    | ~ spl0_6 ),
    inference(subsumption_resolution,[],[f42,f17])).

fof(f17,plain,
    ( k1_xboole_0 != k4_relat_1(k1_xboole_0)
    | spl0_1 ),
    inference(avatar_component_clause,[],[f15])).

fof(f15,plain,
    ( spl0_1
  <=> k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl0_1])])).

fof(f42,plain,
    ( k1_xboole_0 = k4_relat_1(k1_xboole_0)
    | ~ spl0_2
    | ~ spl0_6 ),
    inference(resolution,[],[f40,f22])).

fof(f22,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl0_2 ),
    inference(avatar_component_clause,[],[f20])).

fof(f20,plain,
    ( spl0_2
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl0_2])])).

fof(f40,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k4_relat_1(X0) = k1_xboole_0 )
    | ~ spl0_6 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl0_6
  <=> ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k4_relat_1(X0) = k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl0_6])])).

fof(f41,plain,
    ( spl0_6
    | ~ spl0_3
    | ~ spl0_5 ),
    inference(avatar_split_clause,[],[f37,f33,f25,f39])).

fof(f25,plain,
    ( spl0_3
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl0_3])])).

fof(f33,plain,
    ( spl0_5
  <=> ! [X0] :
        ( v1_xboole_0(k4_relat_1(X0))
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl0_5])])).

fof(f37,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k4_relat_1(X0) = k1_xboole_0 )
    | ~ spl0_3
    | ~ spl0_5 ),
    inference(resolution,[],[f34,f26])).

fof(f26,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl0_3 ),
    inference(avatar_component_clause,[],[f25])).

fof(f34,plain,
    ( ! [X0] :
        ( v1_xboole_0(k4_relat_1(X0))
        | ~ v1_xboole_0(X0) )
    | ~ spl0_5 ),
    inference(avatar_component_clause,[],[f33])).

fof(f35,plain,(
    spl0_5 ),
    inference(avatar_split_clause,[],[f12,f33])).

fof(f12,plain,(
    ! [X0] :
      ( v1_xboole_0(k4_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ( v1_relat_1(k4_relat_1(X0))
        & v1_xboole_0(k4_relat_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ( v1_relat_1(k4_relat_1(X0))
        & v1_xboole_0(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_relat_1)).

fof(f27,plain,(
    spl0_3 ),
    inference(avatar_split_clause,[],[f11,f25])).

fof(f11,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(f23,plain,(
    spl0_2 ),
    inference(avatar_split_clause,[],[f10,f20])).

fof(f10,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f18,plain,(
    ~ spl0_1 ),
    inference(avatar_split_clause,[],[f9,f15])).

fof(f9,plain,(
    k1_xboole_0 != k4_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    k1_xboole_0 != k4_relat_1(k1_xboole_0) ),
    inference(flattening,[],[f5])).

fof(f5,negated_conjecture,(
    k1_xboole_0 != k4_relat_1(k1_xboole_0) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_relat_1)).

%------------------------------------------------------------------------------
