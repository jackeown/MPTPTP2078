%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0037+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:13 EST 2020

% Result     : Theorem 1.42s
% Output     : Refutation 1.42s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 171 expanded)
%              Number of leaves         :   10 (  57 expanded)
%              Depth                    :   12
%              Number of atoms          :  211 ( 421 expanded)
%              Number of equality atoms :   16 (  60 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f503,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f81,f107,f108,f377,f379,f381,f420,f459,f463,f502])).

fof(f502,plain,
    ( spl6_2
    | spl6_3
    | ~ spl6_5 ),
    inference(avatar_contradiction_clause,[],[f501])).

fof(f501,plain,
    ( $false
    | spl6_2
    | spl6_3
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f500,f468])).

fof(f468,plain,
    ( ~ r2_hidden(sK3(sK0,k3_xboole_0(sK2,sK1),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)),sK2)
    | spl6_3 ),
    inference(subsumption_resolution,[],[f402,f467])).

fof(f467,plain,
    ( r2_hidden(sK3(sK0,k3_xboole_0(sK2,sK1),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)),sK1)
    | spl6_3 ),
    inference(subsumption_resolution,[],[f466,f30])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f466,plain,
    ( r2_hidden(sK3(sK0,k3_xboole_0(sK2,sK1),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1))
    | r2_hidden(sK3(sK0,k3_xboole_0(sK2,sK1),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)),sK1)
    | spl6_3 ),
    inference(subsumption_resolution,[],[f333,f106])).

fof(f106,plain,
    ( ~ r2_hidden(sK3(sK0,k3_xboole_0(sK2,sK1),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)),k3_xboole_0(sK2,sK1))
    | spl6_3 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl6_3
  <=> r2_hidden(sK3(sK0,k3_xboole_0(sK2,sK1),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)),k3_xboole_0(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f333,plain,
    ( r2_hidden(sK3(sK0,k3_xboole_0(sK2,sK1),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)),k3_xboole_0(sK2,sK1))
    | r2_hidden(sK3(sK0,k3_xboole_0(sK2,sK1),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1))
    | r2_hidden(sK3(sK0,k3_xboole_0(sK2,sK1),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)),sK1) ),
    inference(resolution,[],[f50,f33])).

fof(f33,plain,(
    ~ sQ5_eqProxy(k2_xboole_0(sK0,k3_xboole_0(sK2,sK1)),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)) ),
    inference(equality_proxy_replacement,[],[f11,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( sQ5_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ5_eqProxy])])).

fof(f11,plain,(
    k2_xboole_0(sK0,k3_xboole_0(sK2,sK1)) != k3_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(X0,k3_xboole_0(X2,X1)) != k3_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,X1)
       => k2_xboole_0(X0,k3_xboole_0(X2,X1)) = k3_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k3_xboole_0(X2,X1)) = k3_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_xboole_1)).

fof(f50,plain,(
    ! [X10,X11] :
      ( sQ5_eqProxy(k2_xboole_0(sK0,X10),X11)
      | r2_hidden(sK3(sK0,X10,X11),X10)
      | r2_hidden(sK3(sK0,X10,X11),X11)
      | r2_hidden(sK3(sK0,X10,X11),sK1) ) ),
    inference(resolution,[],[f44,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | sQ5_eqProxy(k2_xboole_0(X0,X1),X2) ) ),
    inference(equality_proxy_replacement,[],[f16,f32])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f44,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f10,f13])).

fof(f13,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f10,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f402,plain,
    ( ~ r2_hidden(sK3(sK0,k3_xboole_0(sK2,sK1),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)),sK2)
    | ~ r2_hidden(sK3(sK0,k3_xboole_0(sK2,sK1),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)),sK1)
    | spl6_3 ),
    inference(resolution,[],[f106,f29])).

fof(f29,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f500,plain,
    ( r2_hidden(sK3(sK0,k3_xboole_0(sK2,sK1),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)),sK2)
    | spl6_2
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f492,f80])).

fof(f80,plain,
    ( ~ r2_hidden(sK3(sK0,k3_xboole_0(sK2,sK1),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)),sK0)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl6_2
  <=> r2_hidden(sK3(sK0,k3_xboole_0(sK2,sK1),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f492,plain,
    ( r2_hidden(sK3(sK0,k3_xboole_0(sK2,sK1),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)),sK0)
    | r2_hidden(sK3(sK0,k3_xboole_0(sK2,sK1),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)),sK2)
    | ~ spl6_5 ),
    inference(resolution,[],[f375,f28])).

fof(f28,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f17])).

fof(f17,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f375,plain,
    ( r2_hidden(sK3(sK0,k3_xboole_0(sK2,sK1),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)),k2_xboole_0(sK0,sK2))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f374])).

fof(f374,plain,
    ( spl6_5
  <=> r2_hidden(sK3(sK0,k3_xboole_0(sK2,sK1),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)),k2_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f463,plain,
    ( spl6_1
    | ~ spl6_2 ),
    inference(avatar_contradiction_clause,[],[f462])).

fof(f462,plain,
    ( $false
    | spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f461,f424])).

fof(f424,plain,
    ( r2_hidden(sK3(sK0,k3_xboole_0(sK2,sK1),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)),sK1)
    | ~ spl6_2 ),
    inference(resolution,[],[f79,f44])).

fof(f79,plain,
    ( r2_hidden(sK3(sK0,k3_xboole_0(sK2,sK1),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)),sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f461,plain,
    ( ~ r2_hidden(sK3(sK0,k3_xboole_0(sK2,sK1),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)),sK1)
    | spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f432,f428])).

fof(f428,plain,
    ( ! [X2] : r2_hidden(sK3(sK0,k3_xboole_0(sK2,sK1),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)),k2_xboole_0(sK0,X2))
    | ~ spl6_2 ),
    inference(resolution,[],[f79,f27])).

fof(f27,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f18])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f432,plain,
    ( ~ r2_hidden(sK3(sK0,k3_xboole_0(sK2,sK1),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)),k2_xboole_0(sK0,sK2))
    | ~ r2_hidden(sK3(sK0,k3_xboole_0(sK2,sK1),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)),sK1)
    | spl6_1 ),
    inference(resolution,[],[f76,f29])).

fof(f76,plain,
    ( ~ r2_hidden(sK3(sK0,k3_xboole_0(sK2,sK1),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl6_1
  <=> r2_hidden(sK3(sK0,k3_xboole_0(sK2,sK1),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f459,plain,
    ( ~ spl6_2
    | spl6_5 ),
    inference(avatar_contradiction_clause,[],[f458])).

fof(f458,plain,
    ( $false
    | ~ spl6_2
    | spl6_5 ),
    inference(subsumption_resolution,[],[f450,f79])).

fof(f450,plain,
    ( ~ r2_hidden(sK3(sK0,k3_xboole_0(sK2,sK1),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)),sK0)
    | spl6_5 ),
    inference(resolution,[],[f376,f27])).

fof(f376,plain,
    ( ~ r2_hidden(sK3(sK0,k3_xboole_0(sK2,sK1),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)),k2_xboole_0(sK0,sK2))
    | spl6_5 ),
    inference(avatar_component_clause,[],[f374])).

fof(f420,plain,
    ( ~ spl6_1
    | spl6_5 ),
    inference(avatar_contradiction_clause,[],[f419])).

fof(f419,plain,
    ( $false
    | ~ spl6_1
    | spl6_5 ),
    inference(subsumption_resolution,[],[f411,f376])).

fof(f411,plain,
    ( r2_hidden(sK3(sK0,k3_xboole_0(sK2,sK1),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)),k2_xboole_0(sK0,sK2))
    | ~ spl6_1 ),
    inference(resolution,[],[f75,f31])).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f75,plain,
    ( r2_hidden(sK3(sK0,k3_xboole_0(sK2,sK1),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f74])).

fof(f381,plain,
    ( ~ spl6_3
    | spl6_5 ),
    inference(avatar_contradiction_clause,[],[f380])).

fof(f380,plain,
    ( $false
    | ~ spl6_3
    | spl6_5 ),
    inference(subsumption_resolution,[],[f376,f178])).

fof(f178,plain,
    ( ! [X3] : r2_hidden(sK3(sK0,k3_xboole_0(sK2,sK1),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)),k2_xboole_0(X3,sK2))
    | ~ spl6_3 ),
    inference(resolution,[],[f110,f26])).

fof(f26,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f110,plain,
    ( r2_hidden(sK3(sK0,k3_xboole_0(sK2,sK1),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)),sK2)
    | ~ spl6_3 ),
    inference(resolution,[],[f105,f31])).

fof(f105,plain,
    ( r2_hidden(sK3(sK0,k3_xboole_0(sK2,sK1),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)),k3_xboole_0(sK2,sK1))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f104])).

fof(f379,plain,
    ( ~ spl6_3
    | spl6_4 ),
    inference(avatar_contradiction_clause,[],[f378])).

fof(f378,plain,
    ( $false
    | ~ spl6_3
    | spl6_4 ),
    inference(subsumption_resolution,[],[f372,f111])).

fof(f111,plain,
    ( r2_hidden(sK3(sK0,k3_xboole_0(sK2,sK1),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)),sK1)
    | ~ spl6_3 ),
    inference(resolution,[],[f105,f30])).

fof(f372,plain,
    ( ~ r2_hidden(sK3(sK0,k3_xboole_0(sK2,sK1),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)),sK1)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f370])).

fof(f370,plain,
    ( spl6_4
  <=> r2_hidden(sK3(sK0,k3_xboole_0(sK2,sK1),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f377,plain,
    ( ~ spl6_4
    | ~ spl6_5
    | spl6_1 ),
    inference(avatar_split_clause,[],[f96,f74,f374,f370])).

fof(f96,plain,
    ( ~ r2_hidden(sK3(sK0,k3_xboole_0(sK2,sK1),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)),k2_xboole_0(sK0,sK2))
    | ~ r2_hidden(sK3(sK0,k3_xboole_0(sK2,sK1),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)),sK1)
    | spl6_1 ),
    inference(resolution,[],[f76,f29])).

fof(f108,plain,
    ( spl6_1
    | spl6_3
    | spl6_2 ),
    inference(avatar_split_clause,[],[f59,f78,f104,f74])).

fof(f59,plain,
    ( r2_hidden(sK3(sK0,k3_xboole_0(sK2,sK1),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)),sK0)
    | r2_hidden(sK3(sK0,k3_xboole_0(sK2,sK1),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)),k3_xboole_0(sK2,sK1))
    | r2_hidden(sK3(sK0,k3_xboole_0(sK2,sK1),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)) ),
    inference(resolution,[],[f33,f35])).

fof(f107,plain,
    ( ~ spl6_1
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f58,f104,f74])).

fof(f58,plain,
    ( ~ r2_hidden(sK3(sK0,k3_xboole_0(sK2,sK1),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)),k3_xboole_0(sK2,sK1))
    | ~ r2_hidden(sK3(sK0,k3_xboole_0(sK2,sK1),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)) ),
    inference(resolution,[],[f33,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | sQ5_eqProxy(k2_xboole_0(X0,X1),X2) ) ),
    inference(equality_proxy_replacement,[],[f15,f32])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f81,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f57,f78,f74])).

fof(f57,plain,
    ( ~ r2_hidden(sK3(sK0,k3_xboole_0(sK2,sK1),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)),sK0)
    | ~ r2_hidden(sK3(sK0,k3_xboole_0(sK2,sK1),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)),k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)) ),
    inference(resolution,[],[f33,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | sQ5_eqProxy(k2_xboole_0(X0,X1),X2) ) ),
    inference(equality_proxy_replacement,[],[f14,f32])).

fof(f14,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f3])).

%------------------------------------------------------------------------------
