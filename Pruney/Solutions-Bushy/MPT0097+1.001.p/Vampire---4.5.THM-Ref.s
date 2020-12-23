%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0097+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:21 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   15 (  16 expanded)
%              Number of leaves         :    4 (   5 expanded)
%              Depth                    :    5
%              Number of atoms          :   19 (  21 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f13,f16])).

fof(f16,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f15])).

fof(f15,plain,
    ( $false
    | spl2_1 ),
    inference(subsumption_resolution,[],[f14,f7])).

fof(f7,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f14,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK0,sK1),sK1)
    | spl2_1 ),
    inference(forward_demodulation,[],[f12,f8])).

fof(f8,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f12,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)),sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f10])).

fof(f10,plain,
    ( spl2_1
  <=> r1_xboole_0(k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f13,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f6,f10])).

fof(f6,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)),sK1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0,X1] : ~ r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_xboole_1)).

%------------------------------------------------------------------------------
