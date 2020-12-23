%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : xboole_0__t7_xboole_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n030.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:19 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   23 (  28 expanded)
%              Number of leaves         :    5 (   8 expanded)
%              Depth                    :    6
%              Number of atoms          :   41 (  51 expanded)
%              Number of equality atoms :   10 (  14 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f30,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f21,f26,f29])).

fof(f29,plain,
    ( spl2_1
    | ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f28])).

fof(f28,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f27,f20])).

fof(f20,plain,
    ( k1_xboole_0 != sK0
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f19])).

fof(f19,plain,
    ( spl2_1
  <=> k1_xboole_0 != sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f27,plain,
    ( k1_xboole_0 = sK0
    | ~ spl2_2 ),
    inference(resolution,[],[f25,f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_0__t7_xboole_0.p',l13_xboole_0)).

fof(f25,plain,
    ( v1_xboole_0(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f24])).

fof(f24,plain,
    ( spl2_2
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f26,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f22,f24])).

fof(f22,plain,(
    v1_xboole_0(sK0) ),
    inference(resolution,[],[f14,f16])).

fof(f16,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ? [X1] : r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
     => v1_xboole_0(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_0__t7_xboole_0.p',d1_xboole_0)).

fof(f14,plain,(
    ! [X1] : ~ r2_hidden(X1,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ~ ( ! [X1] : ~ r2_hidden(X1,X0)
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_0__t7_xboole_0.p',t7_xboole_0)).

fof(f21,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f13,f19])).

fof(f13,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
