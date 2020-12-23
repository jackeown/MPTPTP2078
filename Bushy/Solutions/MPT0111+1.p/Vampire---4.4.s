%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : xboole_1__t104_xboole_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:19 EDT 2019

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 117 expanded)
%              Number of leaves         :   13 (  44 expanded)
%              Depth                    :   10
%              Number of atoms          :  154 ( 284 expanded)
%              Number of equality atoms :   13 (  35 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f108,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f42,f47,f58,f63,f75,f80,f86,f95,f101,f107])).

fof(f107,plain,
    ( spl2_1
    | spl2_3
    | ~ spl2_10 ),
    inference(avatar_contradiction_clause,[],[f106])).

fof(f106,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_10 ),
    inference(subsumption_resolution,[],[f105,f38])).

fof(f38,plain,
    ( ~ r2_xboole_0(sK0,sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl2_3
  <=> ~ r2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f105,plain,
    ( r2_xboole_0(sK0,sK1)
    | ~ spl2_1
    | ~ spl2_10 ),
    inference(subsumption_resolution,[],[f102,f34])).

fof(f34,plain,
    ( sK0 != sK1
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl2_1
  <=> sK0 != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f102,plain,
    ( sK0 = sK1
    | r2_xboole_0(sK0,sK1)
    | ~ spl2_10 ),
    inference(resolution,[],[f74,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t104_xboole_1.p',d8_xboole_0)).

fof(f74,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl2_10
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f101,plain,
    ( spl2_1
    | spl2_7
    | ~ spl2_8 ),
    inference(avatar_contradiction_clause,[],[f100])).

fof(f100,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_7
    | ~ spl2_8 ),
    inference(subsumption_resolution,[],[f99,f46])).

fof(f46,plain,
    ( ~ r2_xboole_0(sK1,sK0)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl2_7
  <=> ~ r2_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f99,plain,
    ( r2_xboole_0(sK1,sK0)
    | ~ spl2_1
    | ~ spl2_8 ),
    inference(subsumption_resolution,[],[f96,f34])).

fof(f96,plain,
    ( sK0 = sK1
    | r2_xboole_0(sK1,sK0)
    | ~ spl2_8 ),
    inference(resolution,[],[f57,f25])).

fof(f57,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl2_8
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f95,plain,
    ( spl2_10
    | spl2_8
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f88,f84,f56,f73])).

fof(f84,plain,
    ( spl2_4
  <=> r3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f88,plain,
    ( r1_tarski(sK1,sK0)
    | r1_tarski(sK0,sK1)
    | ~ spl2_4 ),
    inference(resolution,[],[f85,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r3_xboole_0(X0,X1)
      | r1_tarski(X1,X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
    <=> ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t104_xboole_1.p',d9_xboole_0)).

fof(f85,plain,
    ( r3_xboole_0(sK0,sK1)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f84])).

fof(f86,plain,
    ( spl2_4
    | spl2_3
    | spl2_7 ),
    inference(avatar_split_clause,[],[f82,f45,f37,f84])).

fof(f82,plain,
    ( r3_xboole_0(sK0,sK1)
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f81,f38])).

fof(f81,plain,
    ( r3_xboole_0(sK0,sK1)
    | r2_xboole_0(sK0,sK1)
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f31,f46])).

fof(f31,plain,
    ( r3_xboole_0(sK0,sK1)
    | r2_xboole_0(sK0,sK1)
    | r2_xboole_0(sK1,sK0) ),
    inference(subsumption_resolution,[],[f17,f30])).

fof(f30,plain,(
    sK0 != sK1 ),
    inference(subsumption_resolution,[],[f29,f22])).

fof(f22,plain,(
    ! [X0] : r3_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] : r3_xboole_0(X0,X0) ),
    inference(rectify,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r3_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t104_xboole_1.p',reflexivity_r3_xboole_0)).

fof(f29,plain,
    ( ~ r3_xboole_0(sK0,sK0)
    | sK0 != sK1 ),
    inference(inner_rewriting,[],[f15])).

fof(f15,plain,
    ( ~ r3_xboole_0(sK0,sK1)
    | sK0 != sK1 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ( r2_xboole_0(X1,X0)
        | X0 = X1
        | r2_xboole_0(X0,X1) )
    <~> r3_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ~ ( ~ r2_xboole_0(X1,X0)
            & X0 != X1
            & ~ r2_xboole_0(X0,X1) )
      <=> r3_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( ~ ( ~ r2_xboole_0(X1,X0)
          & X0 != X1
          & ~ r2_xboole_0(X0,X1) )
    <=> r3_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t104_xboole_1.p',t104_xboole_1)).

fof(f17,plain,
    ( r3_xboole_0(sK0,sK1)
    | r2_xboole_0(sK0,sK1)
    | sK0 = sK1
    | r2_xboole_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f80,plain,
    ( spl2_5
    | ~ spl2_10 ),
    inference(avatar_contradiction_clause,[],[f79])).

fof(f79,plain,
    ( $false
    | ~ spl2_5
    | ~ spl2_10 ),
    inference(subsumption_resolution,[],[f77,f41])).

fof(f41,plain,
    ( ~ r3_xboole_0(sK0,sK1)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl2_5
  <=> ~ r3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f77,plain,
    ( r3_xboole_0(sK0,sK1)
    | ~ spl2_10 ),
    inference(resolution,[],[f74,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r3_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f75,plain,
    ( spl2_10
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f71,f67,f73])).

fof(f67,plain,
    ( spl2_2
  <=> r2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f71,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl2_2 ),
    inference(resolution,[],[f68,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f68,plain,
    ( r2_xboole_0(sK0,sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f63,plain,
    ( spl2_5
    | ~ spl2_8 ),
    inference(avatar_contradiction_clause,[],[f62])).

fof(f62,plain,
    ( $false
    | ~ spl2_5
    | ~ spl2_8 ),
    inference(subsumption_resolution,[],[f61,f41])).

fof(f61,plain,
    ( r3_xboole_0(sK0,sK1)
    | ~ spl2_8 ),
    inference(resolution,[],[f57,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | r3_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f58,plain,
    ( spl2_8
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f54,f50,f56])).

fof(f50,plain,
    ( spl2_6
  <=> r2_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f54,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_6 ),
    inference(resolution,[],[f51,f23])).

fof(f51,plain,
    ( r2_xboole_0(sK1,sK0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f50])).

fof(f47,plain,
    ( ~ spl2_7
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f16,f40,f45])).

fof(f16,plain,
    ( ~ r3_xboole_0(sK0,sK1)
    | ~ r2_xboole_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f42,plain,
    ( ~ spl2_3
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f14,f40,f37])).

fof(f14,plain,
    ( ~ r3_xboole_0(sK0,sK1)
    | ~ r2_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f35,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f30,f33])).
%------------------------------------------------------------------------------
