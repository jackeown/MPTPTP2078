%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0069+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   54 (  83 expanded)
%              Number of leaves         :   15 (  37 expanded)
%              Depth                    :    6
%              Number of atoms          :  124 ( 198 expanded)
%              Number of equality atoms :   20 (  34 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f81,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f24,f28,f32,f36,f40,f44,f53,f70,f76,f80])).

fof(f80,plain,
    ( ~ spl1_3
    | ~ spl1_7
    | ~ spl1_12 ),
    inference(avatar_contradiction_clause,[],[f79])).

fof(f79,plain,
    ( $false
    | ~ spl1_3
    | ~ spl1_7
    | ~ spl1_12 ),
    inference(subsumption_resolution,[],[f78,f31])).

fof(f31,plain,
    ( ! [X0] : ~ r2_xboole_0(X0,X0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl1_3
  <=> ! [X0] : ~ r2_xboole_0(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f78,plain,
    ( r2_xboole_0(o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl1_7
    | ~ spl1_12 ),
    inference(backward_demodulation,[],[f52,f77])).

fof(f77,plain,
    ( o_0_0_xboole_0 = sK0
    | ~ spl1_7
    | ~ spl1_12 ),
    inference(resolution,[],[f75,f52])).

fof(f75,plain,
    ( ! [X0] :
        ( ~ r2_xboole_0(X0,o_0_0_xboole_0)
        | o_0_0_xboole_0 = X0 )
    | ~ spl1_12 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl1_12
  <=> ! [X0] :
        ( o_0_0_xboole_0 = X0
        | ~ r2_xboole_0(X0,o_0_0_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).

fof(f52,plain,
    ( r2_xboole_0(sK0,o_0_0_xboole_0)
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl1_7
  <=> r2_xboole_0(sK0,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f76,plain,
    ( spl1_12
    | ~ spl1_6
    | ~ spl1_11 ),
    inference(avatar_split_clause,[],[f71,f68,f42,f74])).

fof(f42,plain,
    ( spl1_6
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ r2_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f68,plain,
    ( spl1_11
  <=> ! [X0] :
        ( ~ r1_tarski(X0,o_0_0_xboole_0)
        | o_0_0_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).

fof(f71,plain,
    ( ! [X0] :
        ( o_0_0_xboole_0 = X0
        | ~ r2_xboole_0(X0,o_0_0_xboole_0) )
    | ~ spl1_6
    | ~ spl1_11 ),
    inference(resolution,[],[f69,f43])).

fof(f43,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,X1)
        | ~ r2_xboole_0(X0,X1) )
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f42])).

fof(f69,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,o_0_0_xboole_0)
        | o_0_0_xboole_0 = X0 )
    | ~ spl1_11 ),
    inference(avatar_component_clause,[],[f68])).

fof(f70,plain,
    ( spl1_11
    | ~ spl1_2
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f49,f38,f34,f26,f68])).

fof(f26,plain,
    ( spl1_2
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f34,plain,
    ( spl1_4
  <=> ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f38,plain,
    ( spl1_5
  <=> ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f49,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,o_0_0_xboole_0)
        | o_0_0_xboole_0 = X0 )
    | ~ spl1_2
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(forward_demodulation,[],[f46,f45])).

fof(f45,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl1_2
    | ~ spl1_4 ),
    inference(resolution,[],[f35,f27])).

fof(f27,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f26])).

fof(f35,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f34])).

fof(f46,plain,
    ( ! [X0] :
        ( o_0_0_xboole_0 = X0
        | ~ r1_tarski(X0,k1_xboole_0) )
    | ~ spl1_2
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(backward_demodulation,[],[f39,f45])).

fof(f39,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | k1_xboole_0 = X0 )
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f38])).

fof(f53,plain,
    ( spl1_7
    | ~ spl1_1
    | ~ spl1_2
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f48,f34,f26,f22,f51])).

fof(f22,plain,
    ( spl1_1
  <=> r2_xboole_0(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f48,plain,
    ( r2_xboole_0(sK0,o_0_0_xboole_0)
    | ~ spl1_1
    | ~ spl1_2
    | ~ spl1_4 ),
    inference(backward_demodulation,[],[f23,f45])).

fof(f23,plain,
    ( r2_xboole_0(sK0,k1_xboole_0)
    | ~ spl1_1 ),
    inference(avatar_component_clause,[],[f22])).

fof(f44,plain,(
    spl1_6 ),
    inference(avatar_split_clause,[],[f17,f42])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f40,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f15,f38])).

fof(f15,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f36,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f14,f34])).

fof(f14,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(f32,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f16,f30])).

fof(f16,plain,(
    ! [X0] : ~ r2_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] : ~ r2_xboole_0(X0,X0) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : ~ r2_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',irreflexivity_r2_xboole_0)).

fof(f28,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f13,f26])).

fof(f13,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f24,plain,(
    spl1_1 ),
    inference(avatar_split_clause,[],[f12,f22])).

fof(f12,plain,(
    r2_xboole_0(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] : r2_xboole_0(X0,k1_xboole_0) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] : ~ r2_xboole_0(X0,k1_xboole_0) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] : ~ r2_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_xboole_1)).

%------------------------------------------------------------------------------
