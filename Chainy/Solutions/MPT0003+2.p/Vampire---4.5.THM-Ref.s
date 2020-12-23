%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0003+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:02 EST 2020

% Result     : Theorem 1.28s
% Output     : Refutation 1.28s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 116 expanded)
%              Number of leaves         :   12 (  39 expanded)
%              Depth                    :    9
%              Number of atoms          :  156 ( 325 expanded)
%              Number of equality atoms :   19 (  38 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f249,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f79,f97,f101,f143,f162,f224,f248])).

fof(f248,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(avatar_contradiction_clause,[],[f241])).

fof(f241,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(unit_resulting_resolution,[],[f63,f234])).

fof(f234,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(backward_demodulation,[],[f213,f230])).

fof(f230,plain,
    ( o_0_0_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f77,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = o_0_0_xboole_0 ) ),
    inference(definition_unfolding,[],[f48,f54])).

fof(f54,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_xboole_0)).

fof(f48,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f77,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl8_2
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f213,plain,
    ( ~ v1_xboole_0(k3_xboole_0(sK0,sK1))
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(unit_resulting_resolution,[],[f188,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f188,plain,
    ( r2_hidden(sK2,k3_xboole_0(sK0,sK1))
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(forward_demodulation,[],[f180,f61])).

fof(f61,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f180,plain,
    ( r2_hidden(sK2,k3_xboole_0(sK1,sK0))
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(unit_resulting_resolution,[],[f74,f96,f68])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f96,plain,
    ( r2_hidden(sK2,sK1)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl8_3
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f74,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl8_1
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f63,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f224,plain,
    ( spl8_2
    | spl8_4 ),
    inference(avatar_split_clause,[],[f41,f99,f76])).

fof(f99,plain,
    ( spl8_4
  <=> ! [X3] :
        ( ~ r2_hidden(X3,sK0)
        | ~ r2_hidden(X3,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f41,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK0)
      | ~ r2_hidden(X3,sK1)
      | r1_xboole_0(sK0,sK1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ? [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        & ? [X2] :
            ( r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      | ( ! [X3] :
            ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,plain,(
    ~ ! [X0,X1] :
        ( ~ ( r1_xboole_0(X0,X1)
            & ? [X2] :
                ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) ) )
        & ~ ( ! [X3] :
                ~ ( r2_hidden(X3,X1)
                  & r2_hidden(X3,X0) )
            & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ~ ( r1_xboole_0(X0,X1)
            & ? [X2] :
                ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) ) )
        & ~ ( ! [X2] :
                ~ ( r2_hidden(X2,X1)
                  & r2_hidden(X2,X0) )
            & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f28])).

fof(f28,conjecture,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f162,plain,
    ( spl8_2
    | ~ spl8_4 ),
    inference(avatar_contradiction_clause,[],[f149])).

fof(f149,plain,
    ( $false
    | spl8_2
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f105,f106,f100])).

fof(f100,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,sK1)
        | ~ r2_hidden(X3,sK0) )
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f99])).

fof(f106,plain,
    ( r2_hidden(sK4(k3_xboole_0(sK0,sK1)),sK1)
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f86,f69])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k3_xboole_0(X0,X1))
      | r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f86,plain,
    ( r2_hidden(sK4(k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f84,f45])).

fof(f45,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK4(X0),X0) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f84,plain,
    ( ~ v1_xboole_0(k3_xboole_0(sK0,sK1))
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f81,f66])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f52,f54])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f81,plain,
    ( o_0_0_xboole_0 != k3_xboole_0(sK0,sK1)
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f78,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != o_0_0_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f47,f54])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f78,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f105,plain,
    ( r2_hidden(sK4(k3_xboole_0(sK0,sK1)),sK0)
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f86,f70])).

fof(f70,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k3_xboole_0(X0,X1))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f143,plain,
    ( spl8_3
    | spl8_4 ),
    inference(avatar_split_clause,[],[f40,f99,f94])).

fof(f40,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK0)
      | ~ r2_hidden(X3,sK1)
      | r2_hidden(sK2,sK1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f101,plain,
    ( spl8_1
    | spl8_4 ),
    inference(avatar_split_clause,[],[f39,f99,f72])).

fof(f39,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK0)
      | ~ r2_hidden(X3,sK1)
      | r2_hidden(sK2,sK0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f97,plain,
    ( spl8_3
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f38,f76,f94])).

fof(f38,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f79,plain,
    ( spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f37,f76,f72])).

fof(f37,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
