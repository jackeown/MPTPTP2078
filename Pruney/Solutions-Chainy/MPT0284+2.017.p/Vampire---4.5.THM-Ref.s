%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:40 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 177 expanded)
%              Number of leaves         :   29 (  66 expanded)
%              Depth                    :   14
%              Number of atoms          :  157 ( 258 expanded)
%              Number of equality atoms :   41 (  88 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2130,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f256,f266,f331,f371,f2055,f2078,f2125,f2129])).

fof(f2129,plain,(
    spl2_42 ),
    inference(avatar_contradiction_clause,[],[f2127])).

fof(f2127,plain,
    ( $false
    | spl2_42 ),
    inference(unit_resulting_resolution,[],[f1688,f2077,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(f2077,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k3_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | spl2_42 ),
    inference(avatar_component_clause,[],[f2075])).

fof(f2075,plain,
    ( spl2_42
  <=> r1_tarski(k1_zfmisc_1(k3_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).

fof(f1688,plain,(
    ! [X14,X15,X16] : r1_tarski(k3_xboole_0(X16,k3_xboole_0(X14,X15)),X14) ),
    inference(superposition,[],[f32,f113])).

fof(f113,plain,(
    ! [X6,X7,X5] : k3_xboole_0(X5,k3_xboole_0(X6,X7)) = k3_xboole_0(X7,k3_xboole_0(X5,X6)) ),
    inference(superposition,[],[f44,f34])).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f44,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f32,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f2125,plain,(
    spl2_39 ),
    inference(avatar_contradiction_clause,[],[f2120])).

fof(f2120,plain,
    ( $false
    | spl2_39 ),
    inference(unit_resulting_resolution,[],[f66,f2054,f41])).

fof(f2054,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | spl2_39 ),
    inference(avatar_component_clause,[],[f2052])).

fof(f2052,plain,
    ( spl2_39
  <=> r1_tarski(k1_zfmisc_1(k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).

fof(f66,plain,(
    ! [X2,X1] : r1_tarski(k3_xboole_0(X2,X1),X1) ),
    inference(superposition,[],[f32,f34])).

fof(f2078,plain,
    ( ~ spl2_42
    | spl2_3 ),
    inference(avatar_split_clause,[],[f2073,f259,f2075])).

fof(f259,plain,
    ( spl2_3
  <=> r1_tarski(k1_zfmisc_1(k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f2073,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k3_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | spl2_3 ),
    inference(forward_demodulation,[],[f2072,f33])).

fof(f33,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f2072,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k3_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK1,sK0),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | spl2_3 ),
    inference(forward_demodulation,[],[f2071,f44])).

fof(f2071,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k3_xboole_0(k3_xboole_0(sK1,k5_xboole_0(sK1,sK0)),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | spl2_3 ),
    inference(forward_demodulation,[],[f2004,f34])).

fof(f2004,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK1,k5_xboole_0(sK1,sK0)))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | spl2_3 ),
    inference(backward_demodulation,[],[f261,f222])).

fof(f222,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f203,f34])).

fof(f203,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(k5_xboole_0(X0,X1),X0) ),
    inference(superposition,[],[f45,f31])).

fof(f31,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f45,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

fof(f261,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f259])).

fof(f2055,plain,
    ( ~ spl2_39
    | spl2_7 ),
    inference(avatar_split_clause,[],[f2050,f281,f2052])).

fof(f281,plain,
    ( spl2_7
  <=> r1_tarski(k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f2050,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | spl2_7 ),
    inference(forward_demodulation,[],[f2001,f33])).

fof(f2001,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k3_xboole_0(sK1,k5_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | spl2_7 ),
    inference(backward_demodulation,[],[f283,f222])).

fof(f283,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | spl2_7 ),
    inference(avatar_component_clause,[],[f281])).

fof(f371,plain,
    ( ~ spl2_7
    | spl2_4
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f339,f277,f263,f281])).

fof(f263,plain,
    ( spl2_4
  <=> r1_tarski(k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f277,plain,
    ( spl2_6
  <=> r1_tarski(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f339,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | spl2_4
    | ~ spl2_6 ),
    inference(unit_resulting_resolution,[],[f265,f278,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k5_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_xboole_1)).

fof(f278,plain,
    ( r1_tarski(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f277])).

fof(f265,plain,
    ( ~ r1_tarski(k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | spl2_4 ),
    inference(avatar_component_clause,[],[f263])).

fof(f331,plain,(
    spl2_6 ),
    inference(avatar_contradiction_clause,[],[f329])).

fof(f329,plain,
    ( $false
    | spl2_6 ),
    inference(unit_resulting_resolution,[],[f58,f279,f41])).

fof(f279,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | spl2_6 ),
    inference(avatar_component_clause,[],[f277])).

fof(f58,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f35,f38])).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_xboole_1)).

fof(f266,plain,
    ( ~ spl2_3
    | ~ spl2_4
    | spl2_2 ),
    inference(avatar_split_clause,[],[f257,f253,f263,f259])).

fof(f253,plain,
    ( spl2_2
  <=> r1_tarski(k5_xboole_0(k1_zfmisc_1(k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))),k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f257,plain,
    ( ~ r1_tarski(k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | ~ r1_tarski(k1_zfmisc_1(k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | spl2_2 ),
    inference(resolution,[],[f255,f46])).

fof(f255,plain,
    ( ~ r1_tarski(k5_xboole_0(k1_zfmisc_1(k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))),k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f253])).

fof(f256,plain,
    ( ~ spl2_2
    | spl2_1 ),
    inference(avatar_split_clause,[],[f251,f61,f253])).

fof(f61,plain,
    ( spl2_1
  <=> r1_tarski(k3_tarski(k6_enumset1(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f251,plain,
    ( ~ r1_tarski(k5_xboole_0(k1_zfmisc_1(k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))),k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | spl2_1 ),
    inference(forward_demodulation,[],[f250,f39])).

fof(f39,plain,(
    ! [X0,X1] : k1_zfmisc_1(k3_xboole_0(X0,X1)) = k3_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] : k1_zfmisc_1(k3_xboole_0(X0,X1)) = k3_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_zfmisc_1)).

fof(f250,plain,
    ( ~ r1_tarski(k5_xboole_0(k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))),k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | spl2_1 ),
    inference(forward_demodulation,[],[f249,f34])).

fof(f249,plain,
    ( ~ r1_tarski(k5_xboole_0(k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))),k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | spl2_1 ),
    inference(forward_demodulation,[],[f248,f33])).

fof(f248,plain,
    ( ~ r1_tarski(k5_xboole_0(k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | spl2_1 ),
    inference(forward_demodulation,[],[f63,f59])).

fof(f59,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f40,f56])).

fof(f56,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f36,f55])).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f37,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f42,f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f47,f52])).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f48,f51])).

fof(f51,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f49,f50])).

fof(f50,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f42,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f37,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f63,plain,
    ( ~ r1_tarski(k3_tarski(k6_enumset1(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f64,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f57,f61])).

fof(f57,plain,(
    ~ r1_tarski(k3_tarski(k6_enumset1(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f30,f56,f38,f38])).

fof(f30,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f28])).

fof(f28,plain,
    ( ? [X0,X1] : ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1)))
   => ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1] : ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1))) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1))) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:07:54 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.42  % (20088)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.43  % (20081)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.43  % (20080)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.46  % (20090)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.46  % (20079)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.46  % (20077)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (20075)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.47  % (20074)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.48  % (20087)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.48  % (20083)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.48  % (20082)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % (20085)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (20091)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.48  % (20078)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.48  % (20089)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.48  % (20084)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.49  % (20092)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.50  % (20086)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.50  % (20086)Refutation not found, incomplete strategy% (20086)------------------------------
% 0.21/0.50  % (20086)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (20086)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (20086)Memory used [KB]: 10618
% 0.21/0.50  % (20086)Time elapsed: 0.092 s
% 0.21/0.50  % (20086)------------------------------
% 0.21/0.50  % (20086)------------------------------
% 0.21/0.52  % (20081)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f2130,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f64,f256,f266,f331,f371,f2055,f2078,f2125,f2129])).
% 0.21/0.53  fof(f2129,plain,(
% 0.21/0.53    spl2_42),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f2127])).
% 0.21/0.53  fof(f2127,plain,(
% 0.21/0.53    $false | spl2_42),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f1688,f2077,f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,axiom,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).
% 0.21/0.53  fof(f2077,plain,(
% 0.21/0.53    ~r1_tarski(k1_zfmisc_1(k3_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) | spl2_42),
% 0.21/0.53    inference(avatar_component_clause,[],[f2075])).
% 0.21/0.53  fof(f2075,plain,(
% 0.21/0.53    spl2_42 <=> r1_tarski(k1_zfmisc_1(k3_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).
% 0.21/0.53  fof(f1688,plain,(
% 0.21/0.53    ( ! [X14,X15,X16] : (r1_tarski(k3_xboole_0(X16,k3_xboole_0(X14,X15)),X14)) )),
% 0.21/0.53    inference(superposition,[],[f32,f113])).
% 0.21/0.53  fof(f113,plain,(
% 0.21/0.53    ( ! [X6,X7,X5] : (k3_xboole_0(X5,k3_xboole_0(X6,X7)) = k3_xboole_0(X7,k3_xboole_0(X5,X6))) )),
% 0.21/0.53    inference(superposition,[],[f44,f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.21/0.53  fof(f2125,plain,(
% 0.21/0.53    spl2_39),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f2120])).
% 0.21/0.53  fof(f2120,plain,(
% 0.21/0.53    $false | spl2_39),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f66,f2054,f41])).
% 0.21/0.53  fof(f2054,plain,(
% 0.21/0.53    ~r1_tarski(k1_zfmisc_1(k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) | spl2_39),
% 0.21/0.53    inference(avatar_component_clause,[],[f2052])).
% 0.21/0.53  fof(f2052,plain,(
% 0.21/0.53    spl2_39 <=> r1_tarski(k1_zfmisc_1(k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    ( ! [X2,X1] : (r1_tarski(k3_xboole_0(X2,X1),X1)) )),
% 0.21/0.53    inference(superposition,[],[f32,f34])).
% 0.21/0.53  fof(f2078,plain,(
% 0.21/0.53    ~spl2_42 | spl2_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f2073,f259,f2075])).
% 0.21/0.53  fof(f259,plain,(
% 0.21/0.53    spl2_3 <=> r1_tarski(k1_zfmisc_1(k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.53  fof(f2073,plain,(
% 0.21/0.53    ~r1_tarski(k1_zfmisc_1(k3_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) | spl2_3),
% 0.21/0.53    inference(forward_demodulation,[],[f2072,f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 0.21/0.53  fof(f2072,plain,(
% 0.21/0.53    ~r1_tarski(k1_zfmisc_1(k3_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK1,sK0),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) | spl2_3),
% 0.21/0.53    inference(forward_demodulation,[],[f2071,f44])).
% 0.21/0.53  fof(f2071,plain,(
% 0.21/0.53    ~r1_tarski(k1_zfmisc_1(k3_xboole_0(k3_xboole_0(sK1,k5_xboole_0(sK1,sK0)),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) | spl2_3),
% 0.21/0.53    inference(forward_demodulation,[],[f2004,f34])).
% 0.21/0.53  fof(f2004,plain,(
% 0.21/0.53    ~r1_tarski(k1_zfmisc_1(k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK1,k5_xboole_0(sK1,sK0)))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) | spl2_3),
% 0.21/0.53    inference(backward_demodulation,[],[f261,f222])).
% 0.21/0.53  fof(f222,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f203,f34])).
% 0.21/0.53  fof(f203,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(k5_xboole_0(X0,X1),X0)) )),
% 0.21/0.53    inference(superposition,[],[f45,f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.21/0.53    inference(rectify,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).
% 0.21/0.53  fof(f261,plain,(
% 0.21/0.53    ~r1_tarski(k1_zfmisc_1(k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) | spl2_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f259])).
% 0.21/0.53  fof(f2055,plain,(
% 0.21/0.53    ~spl2_39 | spl2_7),
% 0.21/0.53    inference(avatar_split_clause,[],[f2050,f281,f2052])).
% 0.21/0.53  fof(f281,plain,(
% 0.21/0.53    spl2_7 <=> r1_tarski(k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.53  fof(f2050,plain,(
% 0.21/0.53    ~r1_tarski(k1_zfmisc_1(k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) | spl2_7),
% 0.21/0.53    inference(forward_demodulation,[],[f2001,f33])).
% 0.21/0.53  fof(f2001,plain,(
% 0.21/0.53    ~r1_tarski(k1_zfmisc_1(k3_xboole_0(sK1,k5_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) | spl2_7),
% 0.21/0.53    inference(backward_demodulation,[],[f283,f222])).
% 0.21/0.53  fof(f283,plain,(
% 0.21/0.53    ~r1_tarski(k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) | spl2_7),
% 0.21/0.53    inference(avatar_component_clause,[],[f281])).
% 0.21/0.53  fof(f371,plain,(
% 0.21/0.53    ~spl2_7 | spl2_4 | ~spl2_6),
% 0.21/0.53    inference(avatar_split_clause,[],[f339,f277,f263,f281])).
% 0.21/0.53  fof(f263,plain,(
% 0.21/0.53    spl2_4 <=> r1_tarski(k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.53  fof(f277,plain,(
% 0.21/0.53    spl2_6 <=> r1_tarski(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.53  fof(f339,plain,(
% 0.21/0.53    ~r1_tarski(k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) | (spl2_4 | ~spl2_6)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f265,f278,f46])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r1_tarski(k5_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (r1_tarski(k5_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.21/0.53    inference(flattening,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (r1_tarski(k5_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k5_xboole_0(X0,X2),X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_xboole_1)).
% 0.21/0.53  fof(f278,plain,(
% 0.21/0.53    r1_tarski(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) | ~spl2_6),
% 0.21/0.53    inference(avatar_component_clause,[],[f277])).
% 0.21/0.53  fof(f265,plain,(
% 0.21/0.53    ~r1_tarski(k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) | spl2_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f263])).
% 0.21/0.53  fof(f331,plain,(
% 0.21/0.53    spl2_6),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f329])).
% 0.21/0.53  fof(f329,plain,(
% 0.21/0.53    $false | spl2_6),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f58,f279,f41])).
% 0.21/0.53  fof(f279,plain,(
% 0.21/0.53    ~r1_tarski(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) | spl2_6),
% 0.21/0.53    inference(avatar_component_clause,[],[f277])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k5_xboole_0(X0,X1))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f35,f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,axiom,(
% 0.21/0.53    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_xboole_1)).
% 0.21/0.53  fof(f266,plain,(
% 0.21/0.53    ~spl2_3 | ~spl2_4 | spl2_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f257,f253,f263,f259])).
% 0.21/0.53  fof(f253,plain,(
% 0.21/0.53    spl2_2 <=> r1_tarski(k5_xboole_0(k1_zfmisc_1(k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))),k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.53  fof(f257,plain,(
% 0.21/0.53    ~r1_tarski(k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) | ~r1_tarski(k1_zfmisc_1(k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) | spl2_2),
% 0.21/0.53    inference(resolution,[],[f255,f46])).
% 0.21/0.53  fof(f255,plain,(
% 0.21/0.53    ~r1_tarski(k5_xboole_0(k1_zfmisc_1(k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))),k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) | spl2_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f253])).
% 0.21/0.53  fof(f256,plain,(
% 0.21/0.53    ~spl2_2 | spl2_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f251,f61,f253])).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    spl2_1 <=> r1_tarski(k3_tarski(k6_enumset1(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.53  fof(f251,plain,(
% 0.21/0.53    ~r1_tarski(k5_xboole_0(k1_zfmisc_1(k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))),k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) | spl2_1),
% 0.21/0.53    inference(forward_demodulation,[],[f250,f39])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_zfmisc_1(k3_xboole_0(X0,X1)) = k3_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f20])).
% 0.21/0.53  fof(f20,axiom,(
% 0.21/0.53    ! [X0,X1] : k1_zfmisc_1(k3_xboole_0(X0,X1)) = k3_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_zfmisc_1)).
% 0.21/0.53  fof(f250,plain,(
% 0.21/0.53    ~r1_tarski(k5_xboole_0(k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))),k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) | spl2_1),
% 0.21/0.53    inference(forward_demodulation,[],[f249,f34])).
% 0.21/0.53  fof(f249,plain,(
% 0.21/0.53    ~r1_tarski(k5_xboole_0(k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))),k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) | spl2_1),
% 0.21/0.53    inference(forward_demodulation,[],[f248,f33])).
% 0.21/0.53  fof(f248,plain,(
% 0.21/0.53    ~r1_tarski(k5_xboole_0(k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) | spl2_1),
% 0.21/0.53    inference(forward_demodulation,[],[f63,f59])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f40,f56])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f36,f55])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f37,f54])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f42,f53])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f47,f52])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f48,f51])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f49,f50])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,axiom,(
% 0.21/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,axiom,(
% 0.21/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    ~r1_tarski(k3_tarski(k6_enumset1(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) | spl2_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f61])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    ~spl2_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f57,f61])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    ~r1_tarski(k3_tarski(k6_enumset1(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 0.21/0.53    inference(definition_unfolding,[],[f30,f56,f38,f38])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ? [X0,X1] : ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1))) => ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ? [X0,X1] : ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f22])).
% 0.21/0.53  fof(f22,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1)))),
% 0.21/0.53    inference(negated_conjecture,[],[f21])).
% 0.21/0.53  fof(f21,conjecture,(
% 0.21/0.53    ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_zfmisc_1)).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (20081)------------------------------
% 0.21/0.53  % (20081)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (20081)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (20081)Memory used [KB]: 7547
% 0.21/0.53  % (20081)Time elapsed: 0.112 s
% 0.21/0.53  % (20081)------------------------------
% 0.21/0.53  % (20081)------------------------------
% 0.21/0.53  % (20071)Success in time 0.18 s
%------------------------------------------------------------------------------
