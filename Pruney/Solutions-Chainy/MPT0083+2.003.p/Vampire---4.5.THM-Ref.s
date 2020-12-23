%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:11 EST 2020

% Result     : Theorem 1.48s
% Output     : Refutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 172 expanded)
%              Number of leaves         :   19 (  59 expanded)
%              Depth                    :   15
%              Number of atoms          :  157 ( 278 expanded)
%              Number of equality atoms :   39 ( 107 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1683,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f71,f213,f278,f1682])).

fof(f1682,plain,
    ( spl4_3
    | ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f1681])).

fof(f1681,plain,
    ( $false
    | spl4_3
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f1677,f1404])).

fof(f1404,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(forward_demodulation,[],[f1380,f249])).

fof(f249,plain,(
    ! [X1] : k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f85,f30])).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f85,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f81,f52])).

fof(f52,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f44,f29])).

fof(f29,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f44,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f28,f32])).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f28,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f81,plain,(
    ! [X0] : k2_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(superposition,[],[f45,f29])).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f31,f32])).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f1380,plain,(
    ! [X0,X1] : r1_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)),X1) ),
    inference(unit_resulting_resolution,[],[f27,f363,f134])).

fof(f134,plain,(
    ! [X10,X11,X9] :
      ( r1_xboole_0(k2_xboole_0(X10,X11),X9)
      | ~ r1_xboole_0(X9,X11)
      | ~ r1_xboole_0(X9,X10) ) ),
    inference(resolution,[],[f40,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f363,plain,(
    ! [X12,X13] : r1_xboole_0(X12,k4_xboole_0(X13,X12)) ),
    inference(subsumption_resolution,[],[f362,f93])).

fof(f93,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f92,f52])).

fof(f92,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k4_xboole_0(X1,X1)) ),
    inference(forward_demodulation,[],[f88,f29])).

fof(f88,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))) ),
    inference(unit_resulting_resolution,[],[f27,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f35,f32])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f362,plain,(
    ! [X12,X13] :
      ( r2_hidden(sK3(X12,k4_xboole_0(X13,X12)),k1_xboole_0)
      | r1_xboole_0(X12,k4_xboole_0(X13,X12)) ) ),
    inference(forward_demodulation,[],[f353,f52])).

fof(f353,plain,(
    ! [X12,X13] :
      ( r2_hidden(sK3(X12,k4_xboole_0(X13,X12)),k4_xboole_0(X12,X12))
      | r1_xboole_0(X12,k4_xboole_0(X13,X12)) ) ),
    inference(superposition,[],[f48,f182])).

fof(f182,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X3,X2)) = X2 ),
    inference(forward_demodulation,[],[f181,f148])).

fof(f148,plain,(
    ! [X6,X5] : k2_xboole_0(X5,k4_xboole_0(X5,X6)) = X5 ),
    inference(superposition,[],[f45,f46])).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f33,f32])).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f181,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X3,X2)) = k2_xboole_0(X2,k4_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f180,f30])).

fof(f180,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X3,X2)) = k2_xboole_0(k4_xboole_0(X2,X3),X2) ),
    inference(forward_demodulation,[],[f165,f29])).

fof(f165,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X3,X2)) = k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k1_xboole_0)) ),
    inference(superposition,[],[f51,f52])).

fof(f51,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f39,f32])).

fof(f39,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f34,f32])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f27,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f1677,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k4_xboole_0(sK2,sK0))
    | spl4_3
    | ~ spl4_7 ),
    inference(superposition,[],[f428,f277])).

fof(f277,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f275])).

fof(f275,plain,
    ( spl4_7
  <=> sK0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f428,plain,
    ( ! [X2] : ~ r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k4_xboole_0(sK2,k4_xboole_0(X2,sK1)))
    | spl4_3 ),
    inference(superposition,[],[f78,f51])).

fof(f78,plain,
    ( ! [X0] : ~ r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k2_xboole_0(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))))
    | spl4_3 ),
    inference(unit_resulting_resolution,[],[f70,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f70,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl4_3
  <=> r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f278,plain,
    ( spl4_7
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f234,f210,f275])).

fof(f210,plain,
    ( spl4_5
  <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f234,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f222,f29])).

fof(f222,plain,
    ( k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0)
    | ~ spl4_5 ),
    inference(superposition,[],[f46,f212])).

fof(f212,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f210])).

fof(f213,plain,
    ( spl4_5
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f110,f54,f210])).

fof(f54,plain,
    ( spl4_1
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f110,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl4_1 ),
    inference(unit_resulting_resolution,[],[f56,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f37,f32])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f56,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f71,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f43,f68])).

fof(f43,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))) ),
    inference(definition_unfolding,[],[f26,f32,f32])).

fof(f26,plain,(
    ~ r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1))
    & r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1))
        & r1_xboole_0(X0,X1) )
   => ( ~ r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1))
      & r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1))
      & r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,X1)
       => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_xboole_1)).

fof(f57,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f25,f54])).

fof(f25,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:59:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.42  % (2380)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.46  % (2377)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.47  % (2369)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.47  % (2363)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.47  % (2376)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.48  % (2371)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.48  % (2378)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.48  % (2365)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.48  % (2379)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.48  % (2375)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.48  % (2374)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.49  % (2373)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.49  % (2368)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.49  % (2367)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.49  % (2366)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.50  % (2372)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.51  % (2364)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.51  % (2370)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 1.48/0.56  % (2378)Refutation found. Thanks to Tanya!
% 1.48/0.56  % SZS status Theorem for theBenchmark
% 1.48/0.56  % SZS output start Proof for theBenchmark
% 1.48/0.56  fof(f1683,plain,(
% 1.48/0.56    $false),
% 1.48/0.56    inference(avatar_sat_refutation,[],[f57,f71,f213,f278,f1682])).
% 1.48/0.56  fof(f1682,plain,(
% 1.48/0.56    spl4_3 | ~spl4_7),
% 1.48/0.56    inference(avatar_contradiction_clause,[],[f1681])).
% 1.48/0.56  fof(f1681,plain,(
% 1.48/0.56    $false | (spl4_3 | ~spl4_7)),
% 1.48/0.56    inference(subsumption_resolution,[],[f1677,f1404])).
% 1.48/0.56  fof(f1404,plain,(
% 1.48/0.56    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.48/0.56    inference(forward_demodulation,[],[f1380,f249])).
% 1.48/0.56  fof(f249,plain,(
% 1.48/0.56    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = X1) )),
% 1.48/0.56    inference(superposition,[],[f85,f30])).
% 1.48/0.56  fof(f30,plain,(
% 1.48/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f1])).
% 1.48/0.56  fof(f1,axiom,(
% 1.48/0.56    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.48/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.48/0.56  fof(f85,plain,(
% 1.48/0.56    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.48/0.56    inference(forward_demodulation,[],[f81,f52])).
% 1.48/0.56  fof(f52,plain,(
% 1.48/0.56    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.48/0.56    inference(backward_demodulation,[],[f44,f29])).
% 1.48/0.56  fof(f29,plain,(
% 1.48/0.56    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.48/0.56    inference(cnf_transformation,[],[f7])).
% 1.48/0.56  fof(f7,axiom,(
% 1.48/0.56    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.48/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.48/0.56  fof(f44,plain,(
% 1.48/0.56    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 1.48/0.56    inference(definition_unfolding,[],[f28,f32])).
% 1.48/0.56  fof(f32,plain,(
% 1.48/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.48/0.56    inference(cnf_transformation,[],[f9])).
% 1.48/0.56  fof(f9,axiom,(
% 1.48/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.48/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.48/0.56  fof(f28,plain,(
% 1.48/0.56    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f6])).
% 1.48/0.56  fof(f6,axiom,(
% 1.48/0.56    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.48/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 1.48/0.56  fof(f81,plain,(
% 1.48/0.56    ( ! [X0] : (k2_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 1.48/0.56    inference(superposition,[],[f45,f29])).
% 1.48/0.56  fof(f45,plain,(
% 1.48/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0) )),
% 1.48/0.56    inference(definition_unfolding,[],[f31,f32])).
% 1.48/0.56  fof(f31,plain,(
% 1.48/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 1.48/0.56    inference(cnf_transformation,[],[f5])).
% 1.48/0.56  fof(f5,axiom,(
% 1.48/0.56    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 1.48/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 1.48/0.56  fof(f1380,plain,(
% 1.48/0.56    ( ! [X0,X1] : (r1_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,X1)),X1)) )),
% 1.48/0.56    inference(unit_resulting_resolution,[],[f27,f363,f134])).
% 1.48/0.56  fof(f134,plain,(
% 1.48/0.56    ( ! [X10,X11,X9] : (r1_xboole_0(k2_xboole_0(X10,X11),X9) | ~r1_xboole_0(X9,X11) | ~r1_xboole_0(X9,X10)) )),
% 1.48/0.56    inference(resolution,[],[f40,f36])).
% 1.48/0.56  fof(f36,plain,(
% 1.48/0.56    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f18])).
% 1.48/0.56  fof(f18,plain,(
% 1.48/0.56    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.48/0.56    inference(ennf_transformation,[],[f3])).
% 1.48/0.56  fof(f3,axiom,(
% 1.48/0.56    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.48/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.48/0.56  fof(f40,plain,(
% 1.48/0.56    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1) | ~r1_xboole_0(X0,X2)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f19])).
% 1.48/0.56  fof(f19,plain,(
% 1.48/0.56    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.48/0.56    inference(ennf_transformation,[],[f12])).
% 1.48/0.56  fof(f12,axiom,(
% 1.48/0.56    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.48/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).
% 1.48/0.56  fof(f363,plain,(
% 1.48/0.56    ( ! [X12,X13] : (r1_xboole_0(X12,k4_xboole_0(X13,X12))) )),
% 1.48/0.56    inference(subsumption_resolution,[],[f362,f93])).
% 1.48/0.56  fof(f93,plain,(
% 1.48/0.56    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.48/0.56    inference(forward_demodulation,[],[f92,f52])).
% 1.48/0.56  fof(f92,plain,(
% 1.48/0.56    ( ! [X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,X1))) )),
% 1.48/0.56    inference(forward_demodulation,[],[f88,f29])).
% 1.48/0.56  fof(f88,plain,(
% 1.48/0.56    ( ! [X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)))) )),
% 1.48/0.56    inference(unit_resulting_resolution,[],[f27,f47])).
% 1.48/0.56  fof(f47,plain,(
% 1.48/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 1.48/0.56    inference(definition_unfolding,[],[f35,f32])).
% 1.48/0.56  fof(f35,plain,(
% 1.48/0.56    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.48/0.56    inference(cnf_transformation,[],[f23])).
% 1.48/0.56  fof(f23,plain,(
% 1.48/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.48/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f22])).
% 1.48/0.56  fof(f22,plain,(
% 1.48/0.56    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 1.48/0.56    introduced(choice_axiom,[])).
% 1.48/0.56  fof(f17,plain,(
% 1.48/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.48/0.56    inference(ennf_transformation,[],[f15])).
% 1.48/0.56  fof(f15,plain,(
% 1.48/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.48/0.56    inference(rectify,[],[f4])).
% 1.48/0.56  fof(f4,axiom,(
% 1.48/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.48/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.48/0.56  fof(f362,plain,(
% 1.48/0.56    ( ! [X12,X13] : (r2_hidden(sK3(X12,k4_xboole_0(X13,X12)),k1_xboole_0) | r1_xboole_0(X12,k4_xboole_0(X13,X12))) )),
% 1.48/0.56    inference(forward_demodulation,[],[f353,f52])).
% 1.48/0.56  fof(f353,plain,(
% 1.48/0.56    ( ! [X12,X13] : (r2_hidden(sK3(X12,k4_xboole_0(X13,X12)),k4_xboole_0(X12,X12)) | r1_xboole_0(X12,k4_xboole_0(X13,X12))) )),
% 1.48/0.56    inference(superposition,[],[f48,f182])).
% 1.48/0.56  fof(f182,plain,(
% 1.48/0.56    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X3,X2)) = X2) )),
% 1.48/0.56    inference(forward_demodulation,[],[f181,f148])).
% 1.48/0.56  fof(f148,plain,(
% 1.48/0.56    ( ! [X6,X5] : (k2_xboole_0(X5,k4_xboole_0(X5,X6)) = X5) )),
% 1.48/0.56    inference(superposition,[],[f45,f46])).
% 1.48/0.56  fof(f46,plain,(
% 1.48/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.48/0.56    inference(definition_unfolding,[],[f33,f32])).
% 1.48/0.56  fof(f33,plain,(
% 1.48/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f8])).
% 1.48/0.56  fof(f8,axiom,(
% 1.48/0.56    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 1.48/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 1.48/0.56  fof(f181,plain,(
% 1.48/0.56    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X3,X2)) = k2_xboole_0(X2,k4_xboole_0(X2,X3))) )),
% 1.48/0.56    inference(forward_demodulation,[],[f180,f30])).
% 1.48/0.56  fof(f180,plain,(
% 1.48/0.56    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X3,X2)) = k2_xboole_0(k4_xboole_0(X2,X3),X2)) )),
% 1.48/0.56    inference(forward_demodulation,[],[f165,f29])).
% 1.48/0.56  fof(f165,plain,(
% 1.48/0.56    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X3,X2)) = k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k1_xboole_0))) )),
% 1.48/0.56    inference(superposition,[],[f51,f52])).
% 1.48/0.56  fof(f51,plain,(
% 1.48/0.56    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 1.48/0.56    inference(definition_unfolding,[],[f39,f32])).
% 1.48/0.56  fof(f39,plain,(
% 1.48/0.56    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 1.48/0.56    inference(cnf_transformation,[],[f10])).
% 1.48/0.56  fof(f10,axiom,(
% 1.48/0.56    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 1.48/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).
% 1.48/0.56  fof(f48,plain,(
% 1.48/0.56    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r1_xboole_0(X0,X1)) )),
% 1.48/0.56    inference(definition_unfolding,[],[f34,f32])).
% 1.48/0.56  fof(f34,plain,(
% 1.48/0.56    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f23])).
% 1.48/0.56  fof(f27,plain,(
% 1.48/0.56    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f11])).
% 1.48/0.56  fof(f11,axiom,(
% 1.48/0.56    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.48/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.48/0.56  fof(f1677,plain,(
% 1.48/0.56    ~r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k4_xboole_0(sK2,sK0)) | (spl4_3 | ~spl4_7)),
% 1.48/0.56    inference(superposition,[],[f428,f277])).
% 1.48/0.56  fof(f277,plain,(
% 1.48/0.56    sK0 = k4_xboole_0(sK0,sK1) | ~spl4_7),
% 1.48/0.56    inference(avatar_component_clause,[],[f275])).
% 1.48/0.56  fof(f275,plain,(
% 1.48/0.56    spl4_7 <=> sK0 = k4_xboole_0(sK0,sK1)),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.48/0.56  fof(f428,plain,(
% 1.48/0.56    ( ! [X2] : (~r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k4_xboole_0(sK2,k4_xboole_0(X2,sK1)))) ) | spl4_3),
% 1.48/0.56    inference(superposition,[],[f78,f51])).
% 1.48/0.56  fof(f78,plain,(
% 1.48/0.56    ( ! [X0] : (~r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k2_xboole_0(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))))) ) | spl4_3),
% 1.48/0.56    inference(unit_resulting_resolution,[],[f70,f42])).
% 1.48/0.56  fof(f42,plain,(
% 1.48/0.56    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f19])).
% 1.48/0.56  fof(f70,plain,(
% 1.48/0.56    ~r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))) | spl4_3),
% 1.48/0.56    inference(avatar_component_clause,[],[f68])).
% 1.48/0.56  fof(f68,plain,(
% 1.48/0.56    spl4_3 <=> r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)))),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.48/0.56  fof(f278,plain,(
% 1.48/0.56    spl4_7 | ~spl4_5),
% 1.48/0.56    inference(avatar_split_clause,[],[f234,f210,f275])).
% 1.48/0.56  fof(f210,plain,(
% 1.48/0.56    spl4_5 <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.48/0.56  fof(f234,plain,(
% 1.48/0.56    sK0 = k4_xboole_0(sK0,sK1) | ~spl4_5),
% 1.48/0.56    inference(forward_demodulation,[],[f222,f29])).
% 1.48/0.56  fof(f222,plain,(
% 1.48/0.56    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0) | ~spl4_5),
% 1.48/0.56    inference(superposition,[],[f46,f212])).
% 1.48/0.56  fof(f212,plain,(
% 1.48/0.56    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl4_5),
% 1.48/0.56    inference(avatar_component_clause,[],[f210])).
% 1.48/0.56  fof(f213,plain,(
% 1.48/0.56    spl4_5 | ~spl4_1),
% 1.48/0.56    inference(avatar_split_clause,[],[f110,f54,f210])).
% 1.48/0.56  fof(f54,plain,(
% 1.48/0.56    spl4_1 <=> r1_xboole_0(sK0,sK1)),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.48/0.56  fof(f110,plain,(
% 1.48/0.56    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl4_1),
% 1.48/0.56    inference(unit_resulting_resolution,[],[f56,f50])).
% 1.48/0.56  fof(f50,plain,(
% 1.48/0.56    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.48/0.56    inference(definition_unfolding,[],[f37,f32])).
% 1.48/0.56  fof(f37,plain,(
% 1.48/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f24])).
% 1.48/0.56  fof(f24,plain,(
% 1.48/0.56    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.48/0.56    inference(nnf_transformation,[],[f2])).
% 1.48/0.56  fof(f2,axiom,(
% 1.48/0.56    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.48/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.48/0.56  fof(f56,plain,(
% 1.48/0.56    r1_xboole_0(sK0,sK1) | ~spl4_1),
% 1.48/0.56    inference(avatar_component_clause,[],[f54])).
% 1.48/0.56  fof(f71,plain,(
% 1.48/0.56    ~spl4_3),
% 1.48/0.56    inference(avatar_split_clause,[],[f43,f68])).
% 1.48/0.56  fof(f43,plain,(
% 1.48/0.56    ~r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)))),
% 1.48/0.56    inference(definition_unfolding,[],[f26,f32,f32])).
% 1.48/0.56  fof(f26,plain,(
% 1.48/0.56    ~r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1))),
% 1.48/0.56    inference(cnf_transformation,[],[f21])).
% 1.48/0.56  fof(f21,plain,(
% 1.48/0.56    ~r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1)) & r1_xboole_0(sK0,sK1)),
% 1.48/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f20])).
% 1.48/0.56  fof(f20,plain,(
% 1.48/0.56    ? [X0,X1,X2] : (~r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) & r1_xboole_0(X0,X1)) => (~r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1)) & r1_xboole_0(sK0,sK1))),
% 1.48/0.56    introduced(choice_axiom,[])).
% 1.48/0.56  fof(f16,plain,(
% 1.48/0.56    ? [X0,X1,X2] : (~r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) & r1_xboole_0(X0,X1))),
% 1.48/0.56    inference(ennf_transformation,[],[f14])).
% 1.48/0.56  fof(f14,negated_conjecture,(
% 1.48/0.56    ~! [X0,X1,X2] : (r1_xboole_0(X0,X1) => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)))),
% 1.48/0.56    inference(negated_conjecture,[],[f13])).
% 1.48/0.56  fof(f13,conjecture,(
% 1.48/0.56    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)))),
% 1.48/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_xboole_1)).
% 1.48/0.56  fof(f57,plain,(
% 1.48/0.56    spl4_1),
% 1.48/0.56    inference(avatar_split_clause,[],[f25,f54])).
% 1.48/0.56  fof(f25,plain,(
% 1.48/0.56    r1_xboole_0(sK0,sK1)),
% 1.48/0.56    inference(cnf_transformation,[],[f21])).
% 1.48/0.56  % SZS output end Proof for theBenchmark
% 1.48/0.56  % (2378)------------------------------
% 1.48/0.56  % (2378)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.56  % (2378)Termination reason: Refutation
% 1.48/0.56  
% 1.48/0.56  % (2378)Memory used [KB]: 11897
% 1.48/0.56  % (2378)Time elapsed: 0.131 s
% 1.48/0.56  % (2378)------------------------------
% 1.48/0.56  % (2378)------------------------------
% 1.48/0.56  % (2362)Success in time 0.205 s
%------------------------------------------------------------------------------
