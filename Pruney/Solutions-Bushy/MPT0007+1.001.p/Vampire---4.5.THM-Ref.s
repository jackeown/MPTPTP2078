%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0007+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:10 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   21 (  26 expanded)
%              Number of leaves         :    5 (   8 expanded)
%              Depth                    :    6
%              Number of atoms          :   37 (  47 expanded)
%              Number of equality atoms :   10 (  14 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f27,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f16,f22,f26])).

fof(f26,plain,
    ( spl2_1
    | ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f25])).

fof(f25,plain,
    ( $false
    | spl2_1
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f24,f15])).

fof(f15,plain,
    ( k1_xboole_0 != sK0
    | spl2_1 ),
    inference(avatar_component_clause,[],[f13])).

fof(f13,plain,
    ( spl2_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f24,plain,
    ( k1_xboole_0 = sK0
    | ~ spl2_2 ),
    inference(resolution,[],[f21,f9])).

fof(f9,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f21,plain,
    ( v1_xboole_0(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f19])).

fof(f19,plain,
    ( spl2_2
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f22,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f17,f19])).

fof(f17,plain,(
    v1_xboole_0(sK0) ),
    inference(resolution,[],[f8,f10])).

fof(f10,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f8,plain,(
    ! [X1] : ~ r2_hidden(X1,sK0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ~ ( ! [X1] : ~ r2_hidden(X1,X0)
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f16,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f7,f13])).

fof(f7,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f5])).

%------------------------------------------------------------------------------
