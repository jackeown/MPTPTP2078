%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:52 EST 2020

% Result     : Theorem 6.22s
% Output     : Refutation 6.22s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 249 expanded)
%              Number of leaves         :   19 (  93 expanded)
%              Depth                    :   21
%              Number of atoms          :  163 ( 383 expanded)
%              Number of equality atoms :   54 ( 198 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    9 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10054,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f39,f44,f49,f66,f67,f157,f9815,f10021])).

fof(f10021,plain,
    ( spl3_1
    | ~ spl3_87 ),
    inference(avatar_split_clause,[],[f10020,f9812,f36])).

fof(f36,plain,
    ( spl3_1
  <=> r1_tarski(k5_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f9812,plain,
    ( spl3_87
  <=> k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK0,sK2),k3_xboole_0(sK1,k5_xboole_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_87])])).

fof(f10020,plain,
    ( r1_tarski(k5_xboole_0(sK0,sK2),sK1)
    | ~ spl3_87 ),
    inference(forward_demodulation,[],[f10000,f23])).

fof(f23,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f10000,plain,
    ( r1_tarski(k5_xboole_0(sK0,sK2),k5_xboole_0(sK1,k1_xboole_0))
    | ~ spl3_87 ),
    inference(superposition,[],[f273,f9814])).

fof(f9814,plain,
    ( k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK0,sK2),k3_xboole_0(sK1,k5_xboole_0(sK0,sK2)))
    | ~ spl3_87 ),
    inference(avatar_component_clause,[],[f9812])).

fof(f273,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) ),
    inference(superposition,[],[f76,f25])).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f76,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(superposition,[],[f32,f33])).

fof(f33,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f26,f31,f31])).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f28,f27])).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f32,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f24,f31])).

fof(f24,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f9815,plain,
    ( spl3_87
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f9810,f151,f62,f57,f9812])).

fof(f57,plain,
    ( spl3_4
  <=> sK0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f62,plain,
    ( spl3_5
  <=> sK2 = k3_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f151,plain,
    ( spl3_9
  <=> sK2 = k3_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f9810,plain,
    ( k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK0,sK2),k3_xboole_0(sK1,k5_xboole_0(sK0,sK2)))
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f9809,f22])).

fof(f22,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f9809,plain,
    ( k5_xboole_0(sK0,sK0) = k5_xboole_0(k5_xboole_0(sK0,sK2),k3_xboole_0(sK1,k5_xboole_0(sK0,sK2)))
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f9808,f59])).

fof(f59,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f57])).

fof(f9808,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) = k5_xboole_0(k5_xboole_0(sK0,sK2),k3_xboole_0(sK1,k5_xboole_0(sK0,sK2)))
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f9807,f23])).

fof(f9807,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k1_xboole_0))) = k5_xboole_0(k5_xboole_0(sK0,sK2),k3_xboole_0(sK1,k5_xboole_0(sK0,sK2)))
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f9806,f23])).

fof(f9806,plain,
    ( k5_xboole_0(k5_xboole_0(sK0,sK2),k3_xboole_0(sK1,k5_xboole_0(sK0,sK2))) = k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k1_xboole_0))),k1_xboole_0)
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f9805,f52])).

fof(f52,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f21,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f21,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f9805,plain,
    ( k5_xboole_0(k5_xboole_0(sK0,sK2),k3_xboole_0(sK1,k5_xboole_0(sK0,sK2))) = k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k1_xboole_0))),k3_xboole_0(k1_xboole_0,k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k1_xboole_0)))))
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f9804,f383])).

fof(f383,plain,(
    ! [X6] : k5_xboole_0(k1_xboole_0,X6) = X6 ),
    inference(forward_demodulation,[],[f382,f23])).

fof(f382,plain,(
    ! [X6] : k5_xboole_0(X6,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X6) ),
    inference(forward_demodulation,[],[f381,f22])).

fof(f381,plain,(
    ! [X6] : k5_xboole_0(X6,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = k5_xboole_0(k1_xboole_0,X6) ),
    inference(forward_demodulation,[],[f366,f23])).

fof(f366,plain,(
    ! [X6] : k5_xboole_0(X6,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X6,k1_xboole_0)) ),
    inference(superposition,[],[f72,f52])).

fof(f72,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0))) ),
    inference(superposition,[],[f33,f25])).

fof(f9804,plain,
    ( k5_xboole_0(k5_xboole_0(sK0,sK2),k3_xboole_0(sK1,k5_xboole_0(sK0,sK2))) = k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k1_xboole_0))),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k1_xboole_0))))))
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f9803,f22])).

fof(f9803,plain,
    ( k5_xboole_0(k5_xboole_0(sK0,sK2),k3_xboole_0(sK1,k5_xboole_0(sK0,sK2))) = k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)))),k5_xboole_0(k5_xboole_0(sK2,sK2),k3_xboole_0(k5_xboole_0(sK2,sK2),k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)))))))
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f9802,f153])).

fof(f153,plain,
    ( sK2 = k3_xboole_0(sK1,sK2)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f151])).

fof(f9802,plain,
    ( k5_xboole_0(k5_xboole_0(sK0,sK2),k3_xboole_0(sK1,k5_xboole_0(sK0,sK2))) = k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,sK2))))),k5_xboole_0(k5_xboole_0(sK2,sK2),k3_xboole_0(k5_xboole_0(sK2,sK2),k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,sK2))))))))
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f9801,f360])).

fof(f360,plain,(
    ! [X2,X3] : k5_xboole_0(X3,k5_xboole_0(X2,k3_xboole_0(X2,X3))) = k5_xboole_0(X3,k5_xboole_0(X2,k3_xboole_0(X3,X2))) ),
    inference(superposition,[],[f72,f33])).

fof(f9801,plain,
    ( k5_xboole_0(k5_xboole_0(sK0,sK2),k3_xboole_0(sK1,k5_xboole_0(sK0,sK2))) = k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK2,sK1))))),k5_xboole_0(k5_xboole_0(sK2,sK2),k3_xboole_0(k5_xboole_0(sK2,sK2),k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK2,sK1))))))))
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f9660,f33])).

fof(f9660,plain,
    ( k5_xboole_0(k5_xboole_0(sK0,sK2),k3_xboole_0(sK1,k5_xboole_0(sK0,sK2))) = k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))))),k5_xboole_0(k5_xboole_0(sK2,sK2),k3_xboole_0(k5_xboole_0(sK2,sK2),k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))))))))
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(superposition,[],[f739,f64])).

fof(f64,plain,
    ( sK2 = k3_xboole_0(sK2,sK1)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f62])).

fof(f739,plain,
    ( ! [X13] : k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(X13,k5_xboole_0(sK1,k3_xboole_0(sK1,X13))))),k5_xboole_0(k5_xboole_0(X13,k3_xboole_0(X13,sK1)),k3_xboole_0(k5_xboole_0(X13,k3_xboole_0(X13,sK1)),k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(X13,k5_xboole_0(sK1,k3_xboole_0(sK1,X13)))))))) = k5_xboole_0(k5_xboole_0(sK0,X13),k3_xboole_0(sK1,k5_xboole_0(sK0,X13)))
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f738,f25])).

fof(f738,plain,
    ( ! [X13] : k5_xboole_0(k5_xboole_0(sK0,X13),k3_xboole_0(k5_xboole_0(sK0,X13),sK1)) = k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(X13,k5_xboole_0(sK1,k3_xboole_0(sK1,X13))))),k5_xboole_0(k5_xboole_0(X13,k3_xboole_0(X13,sK1)),k3_xboole_0(k5_xboole_0(X13,k3_xboole_0(X13,sK1)),k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(X13,k5_xboole_0(sK1,k3_xboole_0(sK1,X13))))))))
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f737,f23])).

fof(f737,plain,
    ( ! [X13] : k5_xboole_0(k5_xboole_0(sK0,X13),k3_xboole_0(k5_xboole_0(sK0,X13),sK1)) = k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(X13,k5_xboole_0(sK1,k3_xboole_0(sK1,X13))))),k5_xboole_0(k5_xboole_0(X13,k3_xboole_0(X13,k5_xboole_0(sK1,k1_xboole_0))),k3_xboole_0(k5_xboole_0(X13,k3_xboole_0(X13,k5_xboole_0(sK1,k1_xboole_0))),k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(X13,k5_xboole_0(sK1,k3_xboole_0(sK1,X13))))))))
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f671,f22])).

fof(f671,plain,
    ( ! [X13] : k5_xboole_0(k5_xboole_0(sK0,X13),k3_xboole_0(k5_xboole_0(sK0,X13),sK1)) = k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(X13,k5_xboole_0(sK1,k3_xboole_0(sK1,X13))))),k5_xboole_0(k5_xboole_0(X13,k3_xboole_0(X13,k5_xboole_0(sK1,k5_xboole_0(sK0,sK0)))),k3_xboole_0(k5_xboole_0(X13,k3_xboole_0(X13,k5_xboole_0(sK1,k5_xboole_0(sK0,sK0)))),k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(X13,k5_xboole_0(sK1,k3_xboole_0(sK1,X13))))))))
    | ~ spl3_4 ),
    inference(superposition,[],[f105,f59])).

fof(f105,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X2),k3_xboole_0(k5_xboole_0(X0,X2),X1)) = k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2))))),k5_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))))),k3_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))))),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2)))))))) ),
    inference(superposition,[],[f34,f33])).

fof(f34,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(k5_xboole_0(X0,X1),X2)) = k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))),k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))))),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))))),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))))))) ),
    inference(definition_unfolding,[],[f30,f27,f31,f27,f31,f27,f31])).

fof(f30,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k5_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2))) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k5_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_xboole_1)).

fof(f157,plain,
    ( spl3_9
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f146,f62,f151])).

fof(f146,plain,
    ( sK2 = k3_xboole_0(sK1,sK2)
    | ~ spl3_5 ),
    inference(superposition,[],[f25,f64])).

fof(f67,plain,
    ( spl3_4
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f54,f46,f57])).

fof(f46,plain,
    ( spl3_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f54,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl3_3 ),
    inference(resolution,[],[f29,f48])).

fof(f48,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f46])).

fof(f66,plain,
    ( spl3_5
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f53,f41,f62])).

fof(f41,plain,
    ( spl3_2
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f53,plain,
    ( sK2 = k3_xboole_0(sK2,sK1)
    | ~ spl3_2 ),
    inference(resolution,[],[f29,f43])).

fof(f43,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f49,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f18,f46])).

fof(f18,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ~ r1_tarski(k5_xboole_0(sK0,sK2),sK1)
    & r1_tarski(sK2,sK1)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k5_xboole_0(X0,X2),X1)
        & r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k5_xboole_0(sK0,sK2),sK1)
      & r1_tarski(sK2,sK1)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_xboole_0(X0,X2),X1)
      & r1_tarski(X2,X1)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_xboole_0(X0,X2),X1)
      & r1_tarski(X2,X1)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_tarski(X2,X1)
          & r1_tarski(X0,X1) )
       => r1_tarski(k5_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k5_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_xboole_1)).

fof(f44,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f19,f41])).

fof(f19,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f39,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f20,f36])).

fof(f20,plain,(
    ~ r1_tarski(k5_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:19:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.45  % (21648)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.46  % (21643)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.46  % (21638)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (21644)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.47  % (21636)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.47  % (21650)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.47  % (21640)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (21639)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.48  % (21649)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (21645)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.48  % (21637)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.49  % (21653)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.49  % (21651)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.49  % (21642)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (21652)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.49  % (21641)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.49  % (21647)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.51  % (21646)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 5.37/1.03  % (21640)Time limit reached!
% 5.37/1.03  % (21640)------------------------------
% 5.37/1.03  % (21640)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.37/1.03  % (21640)Termination reason: Time limit
% 5.37/1.03  % (21640)Termination phase: Saturation
% 5.37/1.03  
% 5.37/1.03  % (21640)Memory used [KB]: 12153
% 5.37/1.03  % (21640)Time elapsed: 0.600 s
% 5.37/1.03  % (21640)------------------------------
% 5.37/1.03  % (21640)------------------------------
% 6.22/1.14  % (21642)Refutation found. Thanks to Tanya!
% 6.22/1.14  % SZS status Theorem for theBenchmark
% 6.22/1.14  % SZS output start Proof for theBenchmark
% 6.22/1.14  fof(f10054,plain,(
% 6.22/1.14    $false),
% 6.22/1.14    inference(avatar_sat_refutation,[],[f39,f44,f49,f66,f67,f157,f9815,f10021])).
% 6.22/1.14  fof(f10021,plain,(
% 6.22/1.14    spl3_1 | ~spl3_87),
% 6.22/1.14    inference(avatar_split_clause,[],[f10020,f9812,f36])).
% 6.22/1.14  fof(f36,plain,(
% 6.22/1.14    spl3_1 <=> r1_tarski(k5_xboole_0(sK0,sK2),sK1)),
% 6.22/1.14    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 6.22/1.14  fof(f9812,plain,(
% 6.22/1.14    spl3_87 <=> k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK0,sK2),k3_xboole_0(sK1,k5_xboole_0(sK0,sK2)))),
% 6.22/1.14    introduced(avatar_definition,[new_symbols(naming,[spl3_87])])).
% 6.22/1.14  fof(f10020,plain,(
% 6.22/1.14    r1_tarski(k5_xboole_0(sK0,sK2),sK1) | ~spl3_87),
% 6.22/1.14    inference(forward_demodulation,[],[f10000,f23])).
% 6.22/1.14  fof(f23,plain,(
% 6.22/1.14    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 6.22/1.14    inference(cnf_transformation,[],[f6])).
% 6.22/1.14  fof(f6,axiom,(
% 6.22/1.14    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 6.22/1.14    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 6.22/1.14  fof(f10000,plain,(
% 6.22/1.14    r1_tarski(k5_xboole_0(sK0,sK2),k5_xboole_0(sK1,k1_xboole_0)) | ~spl3_87),
% 6.22/1.14    inference(superposition,[],[f273,f9814])).
% 6.22/1.14  fof(f9814,plain,(
% 6.22/1.14    k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK0,sK2),k3_xboole_0(sK1,k5_xboole_0(sK0,sK2))) | ~spl3_87),
% 6.22/1.14    inference(avatar_component_clause,[],[f9812])).
% 6.22/1.14  fof(f273,plain,(
% 6.22/1.14    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0))))) )),
% 6.22/1.14    inference(superposition,[],[f76,f25])).
% 6.22/1.14  fof(f25,plain,(
% 6.22/1.14    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 6.22/1.14    inference(cnf_transformation,[],[f2])).
% 6.22/1.14  fof(f2,axiom,(
% 6.22/1.14    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 6.22/1.14    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 6.22/1.14  fof(f76,plain,(
% 6.22/1.14    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) )),
% 6.22/1.14    inference(superposition,[],[f32,f33])).
% 6.22/1.14  fof(f33,plain,(
% 6.22/1.14    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 6.22/1.14    inference(definition_unfolding,[],[f26,f31,f31])).
% 6.22/1.14  fof(f31,plain,(
% 6.22/1.14    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 6.22/1.14    inference(definition_unfolding,[],[f28,f27])).
% 6.22/1.14  fof(f27,plain,(
% 6.22/1.14    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 6.22/1.14    inference(cnf_transformation,[],[f3])).
% 6.22/1.14  fof(f3,axiom,(
% 6.22/1.14    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 6.22/1.14    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 6.22/1.14  fof(f28,plain,(
% 6.22/1.14    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 6.22/1.14    inference(cnf_transformation,[],[f9])).
% 6.22/1.14  fof(f9,axiom,(
% 6.22/1.14    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 6.22/1.14    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 6.22/1.14  fof(f26,plain,(
% 6.22/1.14    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 6.22/1.14    inference(cnf_transformation,[],[f1])).
% 6.22/1.14  fof(f1,axiom,(
% 6.22/1.14    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 6.22/1.14    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 6.22/1.14  fof(f32,plain,(
% 6.22/1.14    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 6.22/1.14    inference(definition_unfolding,[],[f24,f31])).
% 6.22/1.14  fof(f24,plain,(
% 6.22/1.14    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 6.22/1.14    inference(cnf_transformation,[],[f7])).
% 6.22/1.14  fof(f7,axiom,(
% 6.22/1.14    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 6.22/1.14    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 6.22/1.14  fof(f9815,plain,(
% 6.22/1.14    spl3_87 | ~spl3_4 | ~spl3_5 | ~spl3_9),
% 6.22/1.14    inference(avatar_split_clause,[],[f9810,f151,f62,f57,f9812])).
% 6.22/1.14  fof(f57,plain,(
% 6.22/1.14    spl3_4 <=> sK0 = k3_xboole_0(sK0,sK1)),
% 6.22/1.14    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 6.22/1.14  fof(f62,plain,(
% 6.22/1.14    spl3_5 <=> sK2 = k3_xboole_0(sK2,sK1)),
% 6.22/1.14    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 6.22/1.14  fof(f151,plain,(
% 6.22/1.14    spl3_9 <=> sK2 = k3_xboole_0(sK1,sK2)),
% 6.22/1.14    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 6.22/1.14  fof(f9810,plain,(
% 6.22/1.14    k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK0,sK2),k3_xboole_0(sK1,k5_xboole_0(sK0,sK2))) | (~spl3_4 | ~spl3_5 | ~spl3_9)),
% 6.22/1.14    inference(forward_demodulation,[],[f9809,f22])).
% 6.22/1.14  fof(f22,plain,(
% 6.22/1.14    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 6.22/1.14    inference(cnf_transformation,[],[f8])).
% 6.22/1.14  fof(f8,axiom,(
% 6.22/1.14    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 6.22/1.14    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 6.22/1.14  fof(f9809,plain,(
% 6.22/1.14    k5_xboole_0(sK0,sK0) = k5_xboole_0(k5_xboole_0(sK0,sK2),k3_xboole_0(sK1,k5_xboole_0(sK0,sK2))) | (~spl3_4 | ~spl3_5 | ~spl3_9)),
% 6.22/1.14    inference(forward_demodulation,[],[f9808,f59])).
% 6.22/1.14  fof(f59,plain,(
% 6.22/1.14    sK0 = k3_xboole_0(sK0,sK1) | ~spl3_4),
% 6.22/1.14    inference(avatar_component_clause,[],[f57])).
% 6.22/1.14  fof(f9808,plain,(
% 6.22/1.14    k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) = k5_xboole_0(k5_xboole_0(sK0,sK2),k3_xboole_0(sK1,k5_xboole_0(sK0,sK2))) | (~spl3_4 | ~spl3_5 | ~spl3_9)),
% 6.22/1.14    inference(forward_demodulation,[],[f9807,f23])).
% 6.22/1.14  fof(f9807,plain,(
% 6.22/1.14    k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k1_xboole_0))) = k5_xboole_0(k5_xboole_0(sK0,sK2),k3_xboole_0(sK1,k5_xboole_0(sK0,sK2))) | (~spl3_4 | ~spl3_5 | ~spl3_9)),
% 6.22/1.14    inference(forward_demodulation,[],[f9806,f23])).
% 6.22/1.14  fof(f9806,plain,(
% 6.22/1.14    k5_xboole_0(k5_xboole_0(sK0,sK2),k3_xboole_0(sK1,k5_xboole_0(sK0,sK2))) = k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k1_xboole_0))),k1_xboole_0) | (~spl3_4 | ~spl3_5 | ~spl3_9)),
% 6.22/1.14    inference(forward_demodulation,[],[f9805,f52])).
% 6.22/1.14  fof(f52,plain,(
% 6.22/1.14    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 6.22/1.14    inference(unit_resulting_resolution,[],[f21,f29])).
% 6.22/1.14  fof(f29,plain,(
% 6.22/1.14    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 6.22/1.14    inference(cnf_transformation,[],[f15])).
% 6.22/1.14  fof(f15,plain,(
% 6.22/1.14    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 6.22/1.14    inference(ennf_transformation,[],[f4])).
% 6.22/1.14  fof(f4,axiom,(
% 6.22/1.14    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 6.22/1.14    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 6.22/1.14  fof(f21,plain,(
% 6.22/1.14    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 6.22/1.14    inference(cnf_transformation,[],[f5])).
% 6.22/1.14  fof(f5,axiom,(
% 6.22/1.14    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 6.22/1.14    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 6.22/1.14  fof(f9805,plain,(
% 6.22/1.14    k5_xboole_0(k5_xboole_0(sK0,sK2),k3_xboole_0(sK1,k5_xboole_0(sK0,sK2))) = k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k1_xboole_0))),k3_xboole_0(k1_xboole_0,k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k1_xboole_0))))) | (~spl3_4 | ~spl3_5 | ~spl3_9)),
% 6.22/1.14    inference(forward_demodulation,[],[f9804,f383])).
% 6.22/1.14  fof(f383,plain,(
% 6.22/1.14    ( ! [X6] : (k5_xboole_0(k1_xboole_0,X6) = X6) )),
% 6.22/1.14    inference(forward_demodulation,[],[f382,f23])).
% 6.22/1.14  fof(f382,plain,(
% 6.22/1.14    ( ! [X6] : (k5_xboole_0(X6,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X6)) )),
% 6.22/1.14    inference(forward_demodulation,[],[f381,f22])).
% 6.22/1.14  fof(f381,plain,(
% 6.22/1.14    ( ! [X6] : (k5_xboole_0(X6,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = k5_xboole_0(k1_xboole_0,X6)) )),
% 6.22/1.14    inference(forward_demodulation,[],[f366,f23])).
% 6.22/1.14  fof(f366,plain,(
% 6.22/1.14    ( ! [X6] : (k5_xboole_0(X6,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X6,k1_xboole_0))) )),
% 6.22/1.14    inference(superposition,[],[f72,f52])).
% 6.22/1.14  fof(f72,plain,(
% 6.22/1.14    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) )),
% 6.22/1.14    inference(superposition,[],[f33,f25])).
% 6.22/1.14  fof(f9804,plain,(
% 6.22/1.14    k5_xboole_0(k5_xboole_0(sK0,sK2),k3_xboole_0(sK1,k5_xboole_0(sK0,sK2))) = k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k1_xboole_0))),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k1_xboole_0)))))) | (~spl3_4 | ~spl3_5 | ~spl3_9)),
% 6.22/1.14    inference(forward_demodulation,[],[f9803,f22])).
% 6.22/1.14  fof(f9803,plain,(
% 6.22/1.14    k5_xboole_0(k5_xboole_0(sK0,sK2),k3_xboole_0(sK1,k5_xboole_0(sK0,sK2))) = k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)))),k5_xboole_0(k5_xboole_0(sK2,sK2),k3_xboole_0(k5_xboole_0(sK2,sK2),k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,sK2))))))) | (~spl3_4 | ~spl3_5 | ~spl3_9)),
% 6.22/1.14    inference(forward_demodulation,[],[f9802,f153])).
% 6.22/1.14  fof(f153,plain,(
% 6.22/1.14    sK2 = k3_xboole_0(sK1,sK2) | ~spl3_9),
% 6.22/1.14    inference(avatar_component_clause,[],[f151])).
% 6.22/1.14  fof(f9802,plain,(
% 6.22/1.14    k5_xboole_0(k5_xboole_0(sK0,sK2),k3_xboole_0(sK1,k5_xboole_0(sK0,sK2))) = k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,sK2))))),k5_xboole_0(k5_xboole_0(sK2,sK2),k3_xboole_0(k5_xboole_0(sK2,sK2),k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,sK2)))))))) | (~spl3_4 | ~spl3_5)),
% 6.22/1.14    inference(forward_demodulation,[],[f9801,f360])).
% 6.22/1.14  fof(f360,plain,(
% 6.22/1.14    ( ! [X2,X3] : (k5_xboole_0(X3,k5_xboole_0(X2,k3_xboole_0(X2,X3))) = k5_xboole_0(X3,k5_xboole_0(X2,k3_xboole_0(X3,X2)))) )),
% 6.22/1.14    inference(superposition,[],[f72,f33])).
% 6.22/1.14  fof(f9801,plain,(
% 6.22/1.14    k5_xboole_0(k5_xboole_0(sK0,sK2),k3_xboole_0(sK1,k5_xboole_0(sK0,sK2))) = k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK2,sK1))))),k5_xboole_0(k5_xboole_0(sK2,sK2),k3_xboole_0(k5_xboole_0(sK2,sK2),k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK2,sK1)))))))) | (~spl3_4 | ~spl3_5)),
% 6.22/1.14    inference(forward_demodulation,[],[f9660,f33])).
% 6.22/1.14  fof(f9660,plain,(
% 6.22/1.14    k5_xboole_0(k5_xboole_0(sK0,sK2),k3_xboole_0(sK1,k5_xboole_0(sK0,sK2))) = k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))))),k5_xboole_0(k5_xboole_0(sK2,sK2),k3_xboole_0(k5_xboole_0(sK2,sK2),k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))))))) | (~spl3_4 | ~spl3_5)),
% 6.22/1.14    inference(superposition,[],[f739,f64])).
% 6.22/1.14  fof(f64,plain,(
% 6.22/1.14    sK2 = k3_xboole_0(sK2,sK1) | ~spl3_5),
% 6.22/1.14    inference(avatar_component_clause,[],[f62])).
% 6.22/1.14  fof(f739,plain,(
% 6.22/1.14    ( ! [X13] : (k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(X13,k5_xboole_0(sK1,k3_xboole_0(sK1,X13))))),k5_xboole_0(k5_xboole_0(X13,k3_xboole_0(X13,sK1)),k3_xboole_0(k5_xboole_0(X13,k3_xboole_0(X13,sK1)),k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(X13,k5_xboole_0(sK1,k3_xboole_0(sK1,X13)))))))) = k5_xboole_0(k5_xboole_0(sK0,X13),k3_xboole_0(sK1,k5_xboole_0(sK0,X13)))) ) | ~spl3_4),
% 6.22/1.14    inference(forward_demodulation,[],[f738,f25])).
% 6.22/1.14  fof(f738,plain,(
% 6.22/1.14    ( ! [X13] : (k5_xboole_0(k5_xboole_0(sK0,X13),k3_xboole_0(k5_xboole_0(sK0,X13),sK1)) = k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(X13,k5_xboole_0(sK1,k3_xboole_0(sK1,X13))))),k5_xboole_0(k5_xboole_0(X13,k3_xboole_0(X13,sK1)),k3_xboole_0(k5_xboole_0(X13,k3_xboole_0(X13,sK1)),k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(X13,k5_xboole_0(sK1,k3_xboole_0(sK1,X13))))))))) ) | ~spl3_4),
% 6.22/1.14    inference(forward_demodulation,[],[f737,f23])).
% 6.22/1.14  fof(f737,plain,(
% 6.22/1.14    ( ! [X13] : (k5_xboole_0(k5_xboole_0(sK0,X13),k3_xboole_0(k5_xboole_0(sK0,X13),sK1)) = k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(X13,k5_xboole_0(sK1,k3_xboole_0(sK1,X13))))),k5_xboole_0(k5_xboole_0(X13,k3_xboole_0(X13,k5_xboole_0(sK1,k1_xboole_0))),k3_xboole_0(k5_xboole_0(X13,k3_xboole_0(X13,k5_xboole_0(sK1,k1_xboole_0))),k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(X13,k5_xboole_0(sK1,k3_xboole_0(sK1,X13))))))))) ) | ~spl3_4),
% 6.22/1.14    inference(forward_demodulation,[],[f671,f22])).
% 6.22/1.14  fof(f671,plain,(
% 6.22/1.14    ( ! [X13] : (k5_xboole_0(k5_xboole_0(sK0,X13),k3_xboole_0(k5_xboole_0(sK0,X13),sK1)) = k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(X13,k5_xboole_0(sK1,k3_xboole_0(sK1,X13))))),k5_xboole_0(k5_xboole_0(X13,k3_xboole_0(X13,k5_xboole_0(sK1,k5_xboole_0(sK0,sK0)))),k3_xboole_0(k5_xboole_0(X13,k3_xboole_0(X13,k5_xboole_0(sK1,k5_xboole_0(sK0,sK0)))),k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(X13,k5_xboole_0(sK1,k3_xboole_0(sK1,X13))))))))) ) | ~spl3_4),
% 6.22/1.14    inference(superposition,[],[f105,f59])).
% 6.22/1.14  fof(f105,plain,(
% 6.22/1.14    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X2),k3_xboole_0(k5_xboole_0(X0,X2),X1)) = k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2))))),k5_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))))),k3_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))))),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2))))))))) )),
% 6.22/1.14    inference(superposition,[],[f34,f33])).
% 6.22/1.14  fof(f34,plain,(
% 6.22/1.14    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(k5_xboole_0(X0,X1),X2)) = k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))),k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))))),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))))),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))))))) )),
% 6.22/1.14    inference(definition_unfolding,[],[f30,f27,f31,f27,f31,f27,f31])).
% 6.22/1.14  fof(f30,plain,(
% 6.22/1.14    ( ! [X2,X0,X1] : (k4_xboole_0(k5_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2)))) )),
% 6.22/1.14    inference(cnf_transformation,[],[f10])).
% 6.22/1.14  fof(f10,axiom,(
% 6.22/1.14    ! [X0,X1,X2] : k4_xboole_0(k5_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2)))),
% 6.22/1.14    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_xboole_1)).
% 6.22/1.14  fof(f157,plain,(
% 6.22/1.14    spl3_9 | ~spl3_5),
% 6.22/1.14    inference(avatar_split_clause,[],[f146,f62,f151])).
% 6.22/1.14  fof(f146,plain,(
% 6.22/1.14    sK2 = k3_xboole_0(sK1,sK2) | ~spl3_5),
% 6.22/1.14    inference(superposition,[],[f25,f64])).
% 6.22/1.14  fof(f67,plain,(
% 6.22/1.14    spl3_4 | ~spl3_3),
% 6.22/1.14    inference(avatar_split_clause,[],[f54,f46,f57])).
% 6.22/1.14  fof(f46,plain,(
% 6.22/1.14    spl3_3 <=> r1_tarski(sK0,sK1)),
% 6.22/1.14    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 6.22/1.14  fof(f54,plain,(
% 6.22/1.14    sK0 = k3_xboole_0(sK0,sK1) | ~spl3_3),
% 6.22/1.14    inference(resolution,[],[f29,f48])).
% 6.22/1.14  fof(f48,plain,(
% 6.22/1.14    r1_tarski(sK0,sK1) | ~spl3_3),
% 6.22/1.14    inference(avatar_component_clause,[],[f46])).
% 6.22/1.14  fof(f66,plain,(
% 6.22/1.14    spl3_5 | ~spl3_2),
% 6.22/1.14    inference(avatar_split_clause,[],[f53,f41,f62])).
% 6.22/1.14  fof(f41,plain,(
% 6.22/1.14    spl3_2 <=> r1_tarski(sK2,sK1)),
% 6.22/1.14    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 6.22/1.14  fof(f53,plain,(
% 6.22/1.14    sK2 = k3_xboole_0(sK2,sK1) | ~spl3_2),
% 6.22/1.14    inference(resolution,[],[f29,f43])).
% 6.22/1.14  fof(f43,plain,(
% 6.22/1.14    r1_tarski(sK2,sK1) | ~spl3_2),
% 6.22/1.14    inference(avatar_component_clause,[],[f41])).
% 6.22/1.14  fof(f49,plain,(
% 6.22/1.14    spl3_3),
% 6.22/1.14    inference(avatar_split_clause,[],[f18,f46])).
% 6.22/1.14  fof(f18,plain,(
% 6.22/1.14    r1_tarski(sK0,sK1)),
% 6.22/1.14    inference(cnf_transformation,[],[f17])).
% 6.22/1.14  fof(f17,plain,(
% 6.22/1.14    ~r1_tarski(k5_xboole_0(sK0,sK2),sK1) & r1_tarski(sK2,sK1) & r1_tarski(sK0,sK1)),
% 6.22/1.14    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f16])).
% 6.22/1.14  fof(f16,plain,(
% 6.22/1.14    ? [X0,X1,X2] : (~r1_tarski(k5_xboole_0(X0,X2),X1) & r1_tarski(X2,X1) & r1_tarski(X0,X1)) => (~r1_tarski(k5_xboole_0(sK0,sK2),sK1) & r1_tarski(sK2,sK1) & r1_tarski(sK0,sK1))),
% 6.22/1.14    introduced(choice_axiom,[])).
% 6.22/1.14  fof(f14,plain,(
% 6.22/1.14    ? [X0,X1,X2] : (~r1_tarski(k5_xboole_0(X0,X2),X1) & r1_tarski(X2,X1) & r1_tarski(X0,X1))),
% 6.22/1.14    inference(flattening,[],[f13])).
% 6.22/1.14  fof(f13,plain,(
% 6.22/1.14    ? [X0,X1,X2] : (~r1_tarski(k5_xboole_0(X0,X2),X1) & (r1_tarski(X2,X1) & r1_tarski(X0,X1)))),
% 6.22/1.14    inference(ennf_transformation,[],[f12])).
% 6.22/1.14  fof(f12,negated_conjecture,(
% 6.22/1.14    ~! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k5_xboole_0(X0,X2),X1))),
% 6.22/1.14    inference(negated_conjecture,[],[f11])).
% 6.22/1.14  fof(f11,conjecture,(
% 6.22/1.14    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k5_xboole_0(X0,X2),X1))),
% 6.22/1.14    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_xboole_1)).
% 6.22/1.14  fof(f44,plain,(
% 6.22/1.14    spl3_2),
% 6.22/1.14    inference(avatar_split_clause,[],[f19,f41])).
% 6.22/1.14  fof(f19,plain,(
% 6.22/1.14    r1_tarski(sK2,sK1)),
% 6.22/1.14    inference(cnf_transformation,[],[f17])).
% 6.22/1.14  fof(f39,plain,(
% 6.22/1.14    ~spl3_1),
% 6.22/1.14    inference(avatar_split_clause,[],[f20,f36])).
% 6.22/1.14  fof(f20,plain,(
% 6.22/1.14    ~r1_tarski(k5_xboole_0(sK0,sK2),sK1)),
% 6.22/1.14    inference(cnf_transformation,[],[f17])).
% 6.22/1.14  % SZS output end Proof for theBenchmark
% 6.22/1.14  % (21642)------------------------------
% 6.22/1.14  % (21642)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.22/1.14  % (21642)Termination reason: Refutation
% 6.22/1.14  
% 6.22/1.14  % (21642)Memory used [KB]: 16119
% 6.22/1.14  % (21642)Time elapsed: 0.725 s
% 6.22/1.14  % (21642)------------------------------
% 6.22/1.14  % (21642)------------------------------
% 6.22/1.15  % (21635)Success in time 0.792 s
%------------------------------------------------------------------------------
