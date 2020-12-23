%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0017+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:11 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   45 (  64 expanded)
%              Number of leaves         :   13 (  29 expanded)
%              Depth                    :    6
%              Number of atoms          :   98 ( 144 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f83,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f20,f25,f29,f33,f37,f43,f59,f73,f82])).

fof(f82,plain,
    ( spl3_6
    | ~ spl3_11 ),
    inference(avatar_contradiction_clause,[],[f78])).

fof(f78,plain,
    ( $false
    | spl3_6
    | ~ spl3_11 ),
    inference(resolution,[],[f72,f42])).

fof(f42,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | spl3_6 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl3_6
  <=> r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f72,plain,
    ( ! [X0] : r1_tarski(sK0,k2_xboole_0(sK1,X0))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl3_11
  <=> ! [X0] : r1_tarski(sK0,k2_xboole_0(sK1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f73,plain,
    ( spl3_11
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f68,f57,f27,f71])).

fof(f27,plain,
    ( spl3_3
  <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f57,plain,
    ( spl3_8
  <=> ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | r1_tarski(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f68,plain,
    ( ! [X0] : r1_tarski(sK0,k2_xboole_0(sK1,X0))
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(resolution,[],[f58,f28])).

fof(f28,plain,
    ( ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f27])).

fof(f58,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | r1_tarski(sK0,X0) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f57])).

fof(f59,plain,
    ( spl3_8
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f53,f35,f22,f57])).

fof(f22,plain,
    ( spl3_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f35,plain,
    ( spl3_5
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,X2)
        | ~ r1_tarski(X1,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f53,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | r1_tarski(sK0,X0) )
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(resolution,[],[f36,f24])).

fof(f24,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f22])).

fof(f36,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_tarski(X1,X2)
        | r1_tarski(X0,X2) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f35])).

fof(f43,plain,
    ( ~ spl3_6
    | spl3_1
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f38,f31,f17,f40])).

fof(f17,plain,
    ( spl3_1
  <=> r1_tarski(sK0,k2_xboole_0(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f31,plain,
    ( spl3_4
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f38,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | spl3_1
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f19,f32])).

fof(f32,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f31])).

fof(f19,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(sK2,sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f17])).

fof(f37,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f15,f35])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f33,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f14,f31])).

fof(f14,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f29,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f13,f27])).

fof(f13,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f25,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f11,f22])).

fof(f11,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(sK2,sK1))
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,k2_xboole_0(X2,X1))
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(sK0,k2_xboole_0(sK2,sK1))
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,k2_xboole_0(X2,X1))
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,X1)
       => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f20,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f12,f17])).

fof(f12,plain,(
    ~ r1_tarski(sK0,k2_xboole_0(sK2,sK1)) ),
    inference(cnf_transformation,[],[f10])).

%------------------------------------------------------------------------------
