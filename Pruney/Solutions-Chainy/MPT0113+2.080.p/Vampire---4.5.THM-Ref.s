%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:43 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 555 expanded)
%              Number of leaves         :   20 ( 204 expanded)
%              Depth                    :   19
%              Number of atoms          :  219 ( 784 expanded)
%              Number of equality atoms :   80 ( 507 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3079,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f56,f64,f71,f533,f554,f3029,f3066])).

fof(f3066,plain,
    ( spl3_5
    | ~ spl3_4
    | ~ spl3_20
    | ~ spl3_31 ),
    inference(avatar_split_clause,[],[f3065,f2147,f543,f60,f68])).

fof(f68,plain,
    ( spl3_5
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f60,plain,
    ( spl3_4
  <=> sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f543,plain,
    ( spl3_20
  <=> sK0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f2147,plain,
    ( spl3_31
  <=> sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f3065,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK2)
    | ~ spl3_4
    | ~ spl3_20
    | ~ spl3_31 ),
    inference(forward_demodulation,[],[f3049,f24])).

fof(f24,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f3049,plain,
    ( k3_xboole_0(sK0,sK2) = k5_xboole_0(sK0,sK0)
    | ~ spl3_4
    | ~ spl3_20
    | ~ spl3_31 ),
    inference(superposition,[],[f2464,f2149])).

fof(f2149,plain,
    ( sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f2147])).

fof(f2464,plain,
    ( ! [X1] : k3_xboole_0(sK0,X1) = k5_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,X1)))
    | ~ spl3_4
    | ~ spl3_20 ),
    inference(backward_demodulation,[],[f2171,f2407])).

fof(f2407,plain,
    ( ! [X3] : k2_xboole_0(k1_xboole_0,X3) = X3
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f2406,f24])).

fof(f2406,plain,
    ( ! [X3] : k2_xboole_0(k5_xboole_0(X3,X3),X3) = X3
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f2360,f650])).

fof(f650,plain,
    ( ! [X0] : k3_xboole_0(X0,X0) = X0
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f524,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f524,plain,
    ( ! [X3] : r1_tarski(X3,X3)
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f513,f25])).

fof(f25,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f513,plain,
    ( ! [X3] : r1_tarski(k5_xboole_0(X3,k1_xboole_0),X3)
    | ~ spl3_4 ),
    inference(superposition,[],[f209,f133])).

fof(f133,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f132,f24])).

fof(f132,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k5_xboole_0(sK0,sK0))
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f127,f24])).

fof(f127,plain,
    ( ! [X0] : k3_xboole_0(X0,k5_xboole_0(sK0,sK0)) = k5_xboole_0(k3_xboole_0(X0,sK0),k3_xboole_0(X0,sK0))
    | ~ spl3_4 ),
    inference(superposition,[],[f118,f62])).

fof(f62,plain,
    ( sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f60])).

fof(f118,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2))) ),
    inference(forward_demodulation,[],[f41,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f41,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(definition_unfolding,[],[f33,f27,f27])).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f33,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f209,plain,
    ( ! [X4,X3] : r1_tarski(k5_xboole_0(X3,k3_xboole_0(X3,X4)),X3)
    | ~ spl3_4 ),
    inference(superposition,[],[f96,f168])).

fof(f168,plain,
    ( ! [X2,X0,X1] : k2_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X0)),k3_xboole_0(X2,k2_xboole_0(X0,X1))) = X2
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f167,f25])).

fof(f167,plain,
    ( ! [X2,X0,X1] : k2_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X0)),k3_xboole_0(X2,k2_xboole_0(X0,X1))) = k5_xboole_0(X2,k1_xboole_0)
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f153,f133])).

fof(f153,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X0)),k3_xboole_0(X2,k2_xboole_0(X0,X1))) = k5_xboole_0(X2,k3_xboole_0(X2,k1_xboole_0)) ),
    inference(superposition,[],[f42,f38])).

fof(f38,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k2_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f26,f27])).

fof(f26,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f42,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X2)) ),
    inference(definition_unfolding,[],[f35,f27,f27,f27])).

fof(f35,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f96,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(unit_resulting_resolution,[],[f38,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f31,f27])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f2360,plain,
    ( ! [X3] : k2_xboole_0(k5_xboole_0(X3,k3_xboole_0(X3,X3)),X3) = X3
    | ~ spl3_4 ),
    inference(superposition,[],[f168,f190])).

fof(f190,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(unit_resulting_resolution,[],[f96,f28])).

fof(f2171,plain,
    ( ! [X1] : k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X1)) = k5_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,X1)))
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f590,f2062])).

fof(f2062,plain,
    ( ! [X6] : k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,X6))) = k5_xboole_0(sK0,k3_xboole_0(sK0,X6))
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f578,f572])).

fof(f572,plain,
    ( ! [X0] : k3_xboole_0(sK0,X0) = k3_xboole_0(sK0,k3_xboole_0(sK1,X0))
    | ~ spl3_20 ),
    inference(superposition,[],[f34,f545])).

fof(f545,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f543])).

fof(f578,plain,
    ( ! [X6] : k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,X6))) = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(sK1,X6)))
    | ~ spl3_20 ),
    inference(superposition,[],[f118,f545])).

fof(f590,plain,
    ( ! [X1] : k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,X1)))) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X1))
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f574,f24])).

fof(f574,plain,
    ( ! [X1] : k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,X1)))) = k2_xboole_0(k5_xboole_0(sK0,sK0),k3_xboole_0(sK0,X1))
    | ~ spl3_20 ),
    inference(superposition,[],[f42,f545])).

fof(f3029,plain,
    ( spl3_31
    | ~ spl3_4
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f3004,f543,f60,f2147])).

fof(f3004,plain,
    ( sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))
    | ~ spl3_4
    | ~ spl3_20 ),
    inference(superposition,[],[f2996,f437])).

fof(f437,plain,
    ( ! [X10,X8,X11,X9] : k5_xboole_0(X8,k3_xboole_0(X8,k3_xboole_0(X9,k5_xboole_0(X10,k3_xboole_0(X10,k2_xboole_0(k3_xboole_0(X9,X10),X11)))))) = X8
    | ~ spl3_4 ),
    inference(superposition,[],[f164,f168])).

fof(f164,plain,(
    ! [X4,X2,X3,X1] : k2_xboole_0(k5_xboole_0(X4,k3_xboole_0(X4,k3_xboole_0(X1,X2))),k3_xboole_0(X4,X3)) = k5_xboole_0(X4,k3_xboole_0(X4,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))))) ),
    inference(forward_demodulation,[],[f151,f118])).

fof(f151,plain,(
    ! [X4,X2,X3,X1] : k2_xboole_0(k5_xboole_0(X4,k3_xboole_0(X4,k3_xboole_0(X1,X2))),k3_xboole_0(X4,X3)) = k5_xboole_0(X4,k3_xboole_0(X4,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X2,X3))))) ),
    inference(superposition,[],[f42,f34])).

fof(f2996,plain,
    ( ! [X0] : sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK2,k3_xboole_0(sK2,X0))))
    | ~ spl3_4
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f2995,f2198])).

fof(f2198,plain,
    ( ! [X2,X3] : k2_xboole_0(X2,k3_xboole_0(X2,X3)) = X2
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f2197,f25])).

fof(f2197,plain,
    ( ! [X2,X3] : k5_xboole_0(X2,k1_xboole_0) = k2_xboole_0(X2,k3_xboole_0(X2,X3))
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f2196,f133])).

fof(f2196,plain,
    ( ! [X2,X3] : k5_xboole_0(X2,k3_xboole_0(X2,k1_xboole_0)) = k2_xboole_0(X2,k3_xboole_0(X2,X3))
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f2195,f24])).

fof(f2195,plain,
    ( ! [X2,X3] : k2_xboole_0(X2,k3_xboole_0(X2,X3)) = k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(k1_xboole_0,k1_xboole_0)))
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f922,f567])).

fof(f567,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f514,f28])).

fof(f514,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl3_4 ),
    inference(superposition,[],[f209,f38])).

fof(f922,plain,
    ( ! [X2,X3] : k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X3)))) = k2_xboole_0(X2,k3_xboole_0(X2,X3))
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f861,f168])).

fof(f861,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X0)),k3_xboole_0(X2,k2_xboole_0(X0,X1))),k3_xboole_0(X2,X3)) = k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X3)))) ),
    inference(superposition,[],[f158,f38])).

fof(f158,plain,(
    ! [X6,X4,X5,X3] : k5_xboole_0(X3,k3_xboole_0(X3,k5_xboole_0(k5_xboole_0(X4,k3_xboole_0(X4,X5)),k3_xboole_0(k5_xboole_0(X4,k3_xboole_0(X4,X5)),X6)))) = k2_xboole_0(k2_xboole_0(k5_xboole_0(X3,k3_xboole_0(X3,X4)),k3_xboole_0(X3,X5)),k3_xboole_0(X3,X6)) ),
    inference(superposition,[],[f42,f42])).

fof(f2995,plain,
    ( ! [X0] : k2_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(sK1,X0))) = k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK2,k3_xboole_0(sK2,X0))))
    | ~ spl3_4
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f823,f572])).

fof(f823,plain,
    ( ! [X0] : k2_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(sK1,X0))) = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK2,X0)))))
    | ~ spl3_4
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f783,f545])).

fof(f783,plain,
    ( ! [X0] : k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK2,X0))))) = k2_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(sK1,X0)))
    | ~ spl3_4 ),
    inference(superposition,[],[f171,f62])).

fof(f171,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))))) = k2_xboole_0(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),k3_xboole_0(X0,k3_xboole_0(X1,X3))) ),
    inference(forward_demodulation,[],[f170,f118])).

fof(f170,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))))) = k2_xboole_0(k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2))),k3_xboole_0(X0,k3_xboole_0(X1,X3))) ),
    inference(forward_demodulation,[],[f169,f34])).

fof(f169,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))))) = k2_xboole_0(k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)),k3_xboole_0(X0,k3_xboole_0(X1,X3))) ),
    inference(forward_demodulation,[],[f155,f34])).

fof(f155,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)),k3_xboole_0(k3_xboole_0(X0,X1),X3)) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))))) ),
    inference(superposition,[],[f42,f34])).

fof(f554,plain,
    ( spl3_20
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f541,f44,f543])).

fof(f44,plain,
    ( spl3_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f541,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl3_1 ),
    inference(resolution,[],[f45,f28])).

fof(f45,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f44])).

fof(f533,plain,
    ( spl3_1
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f498,f60,f53,f44])).

fof(f53,plain,
    ( spl3_3
  <=> r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f498,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f55,f209,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f55,plain,
    ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f53])).

fof(f71,plain,
    ( ~ spl3_5
    | spl3_2 ),
    inference(avatar_split_clause,[],[f65,f48,f68])).

fof(f48,plain,
    ( spl3_2
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f65,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,sK2)
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f50,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f50,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f48])).

fof(f64,plain,
    ( spl3_4
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f58,f53,f60])).

fof(f58,plain,
    ( sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
    | ~ spl3_3 ),
    inference(resolution,[],[f28,f55])).

fof(f56,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f37,f53])).

fof(f37,plain,(
    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f22,f27])).

fof(f22,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ( ~ r1_xboole_0(sK0,sK2)
      | ~ r1_tarski(sK0,sK1) )
    & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_tarski(sK0,sK1) )
      & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f51,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f23,f48,f44])).

fof(f23,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:24:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.44  % (24297)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.45  % (24291)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.45  % (24295)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.45  % (24298)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.45  % (24303)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.45  % (24305)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.45  % (24296)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.45  % (24294)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.46  % (24308)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.46  % (24293)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.46  % (24300)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.46  % (24302)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.46  % (24306)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.46  % (24292)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (24307)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.47  % (24299)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.47  % (24290)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.47  % (24301)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 1.36/0.56  % (24296)Refutation found. Thanks to Tanya!
% 1.36/0.56  % SZS status Theorem for theBenchmark
% 1.36/0.56  % SZS output start Proof for theBenchmark
% 1.36/0.56  fof(f3079,plain,(
% 1.36/0.56    $false),
% 1.36/0.56    inference(avatar_sat_refutation,[],[f51,f56,f64,f71,f533,f554,f3029,f3066])).
% 1.36/0.56  fof(f3066,plain,(
% 1.36/0.56    spl3_5 | ~spl3_4 | ~spl3_20 | ~spl3_31),
% 1.36/0.56    inference(avatar_split_clause,[],[f3065,f2147,f543,f60,f68])).
% 1.36/0.56  fof(f68,plain,(
% 1.36/0.56    spl3_5 <=> k1_xboole_0 = k3_xboole_0(sK0,sK2)),
% 1.36/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.36/0.56  fof(f60,plain,(
% 1.36/0.56    spl3_4 <=> sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 1.36/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.36/0.56  fof(f543,plain,(
% 1.36/0.56    spl3_20 <=> sK0 = k3_xboole_0(sK0,sK1)),
% 1.36/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 1.36/0.56  fof(f2147,plain,(
% 1.36/0.56    spl3_31 <=> sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))),
% 1.36/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 1.36/0.56  fof(f3065,plain,(
% 1.36/0.56    k1_xboole_0 = k3_xboole_0(sK0,sK2) | (~spl3_4 | ~spl3_20 | ~spl3_31)),
% 1.36/0.56    inference(forward_demodulation,[],[f3049,f24])).
% 1.36/0.56  fof(f24,plain,(
% 1.36/0.56    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.36/0.56    inference(cnf_transformation,[],[f11])).
% 1.36/0.56  fof(f11,axiom,(
% 1.36/0.56    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.36/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.36/0.56  fof(f3049,plain,(
% 1.36/0.56    k3_xboole_0(sK0,sK2) = k5_xboole_0(sK0,sK0) | (~spl3_4 | ~spl3_20 | ~spl3_31)),
% 1.36/0.56    inference(superposition,[],[f2464,f2149])).
% 1.36/0.56  fof(f2149,plain,(
% 1.36/0.56    sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) | ~spl3_31),
% 1.36/0.56    inference(avatar_component_clause,[],[f2147])).
% 1.36/0.56  fof(f2464,plain,(
% 1.36/0.56    ( ! [X1] : (k3_xboole_0(sK0,X1) = k5_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,X1)))) ) | (~spl3_4 | ~spl3_20)),
% 1.36/0.56    inference(backward_demodulation,[],[f2171,f2407])).
% 1.36/0.56  fof(f2407,plain,(
% 1.36/0.56    ( ! [X3] : (k2_xboole_0(k1_xboole_0,X3) = X3) ) | ~spl3_4),
% 1.36/0.56    inference(forward_demodulation,[],[f2406,f24])).
% 1.36/0.56  fof(f2406,plain,(
% 1.36/0.56    ( ! [X3] : (k2_xboole_0(k5_xboole_0(X3,X3),X3) = X3) ) | ~spl3_4),
% 1.36/0.56    inference(forward_demodulation,[],[f2360,f650])).
% 1.36/0.56  fof(f650,plain,(
% 1.36/0.56    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) ) | ~spl3_4),
% 1.36/0.56    inference(unit_resulting_resolution,[],[f524,f28])).
% 1.36/0.56  fof(f28,plain,(
% 1.36/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.36/0.56    inference(cnf_transformation,[],[f15])).
% 1.36/0.56  fof(f15,plain,(
% 1.36/0.56    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.36/0.56    inference(ennf_transformation,[],[f6])).
% 1.36/0.56  fof(f6,axiom,(
% 1.36/0.56    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.36/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.36/0.56  fof(f524,plain,(
% 1.36/0.56    ( ! [X3] : (r1_tarski(X3,X3)) ) | ~spl3_4),
% 1.36/0.56    inference(forward_demodulation,[],[f513,f25])).
% 1.36/0.56  fof(f25,plain,(
% 1.36/0.56    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.36/0.56    inference(cnf_transformation,[],[f10])).
% 1.36/0.56  fof(f10,axiom,(
% 1.36/0.56    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.36/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.36/0.56  fof(f513,plain,(
% 1.36/0.56    ( ! [X3] : (r1_tarski(k5_xboole_0(X3,k1_xboole_0),X3)) ) | ~spl3_4),
% 1.36/0.56    inference(superposition,[],[f209,f133])).
% 1.36/0.56  fof(f133,plain,(
% 1.36/0.56    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) ) | ~spl3_4),
% 1.36/0.56    inference(forward_demodulation,[],[f132,f24])).
% 1.36/0.56  fof(f132,plain,(
% 1.36/0.56    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k5_xboole_0(sK0,sK0))) ) | ~spl3_4),
% 1.36/0.56    inference(forward_demodulation,[],[f127,f24])).
% 1.36/0.56  fof(f127,plain,(
% 1.36/0.56    ( ! [X0] : (k3_xboole_0(X0,k5_xboole_0(sK0,sK0)) = k5_xboole_0(k3_xboole_0(X0,sK0),k3_xboole_0(X0,sK0))) ) | ~spl3_4),
% 1.36/0.56    inference(superposition,[],[f118,f62])).
% 1.36/0.56  fof(f62,plain,(
% 1.36/0.56    sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) | ~spl3_4),
% 1.36/0.56    inference(avatar_component_clause,[],[f60])).
% 1.36/0.56  fof(f118,plain,(
% 1.36/0.56    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2)))) )),
% 1.36/0.56    inference(forward_demodulation,[],[f41,f34])).
% 1.36/0.56  fof(f34,plain,(
% 1.36/0.56    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 1.36/0.56    inference(cnf_transformation,[],[f4])).
% 1.36/0.56  fof(f4,axiom,(
% 1.36/0.56    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 1.36/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).
% 1.36/0.56  fof(f41,plain,(
% 1.36/0.56    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 1.36/0.56    inference(definition_unfolding,[],[f33,f27,f27])).
% 1.36/0.56  fof(f27,plain,(
% 1.36/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.36/0.56    inference(cnf_transformation,[],[f3])).
% 1.36/0.56  fof(f3,axiom,(
% 1.36/0.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.36/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.36/0.56  fof(f33,plain,(
% 1.36/0.56    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 1.36/0.56    inference(cnf_transformation,[],[f8])).
% 1.36/0.56  fof(f8,axiom,(
% 1.36/0.56    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 1.36/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 1.36/0.56  fof(f209,plain,(
% 1.36/0.56    ( ! [X4,X3] : (r1_tarski(k5_xboole_0(X3,k3_xboole_0(X3,X4)),X3)) ) | ~spl3_4),
% 1.36/0.56    inference(superposition,[],[f96,f168])).
% 1.36/0.56  fof(f168,plain,(
% 1.36/0.56    ( ! [X2,X0,X1] : (k2_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X0)),k3_xboole_0(X2,k2_xboole_0(X0,X1))) = X2) ) | ~spl3_4),
% 1.36/0.56    inference(forward_demodulation,[],[f167,f25])).
% 1.36/0.56  fof(f167,plain,(
% 1.36/0.56    ( ! [X2,X0,X1] : (k2_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X0)),k3_xboole_0(X2,k2_xboole_0(X0,X1))) = k5_xboole_0(X2,k1_xboole_0)) ) | ~spl3_4),
% 1.36/0.56    inference(forward_demodulation,[],[f153,f133])).
% 1.36/0.56  fof(f153,plain,(
% 1.36/0.56    ( ! [X2,X0,X1] : (k2_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X0)),k3_xboole_0(X2,k2_xboole_0(X0,X1))) = k5_xboole_0(X2,k3_xboole_0(X2,k1_xboole_0))) )),
% 1.36/0.56    inference(superposition,[],[f42,f38])).
% 1.36/0.56  fof(f38,plain,(
% 1.36/0.56    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k2_xboole_0(X0,X1)))) )),
% 1.36/0.56    inference(definition_unfolding,[],[f26,f27])).
% 1.36/0.56  fof(f26,plain,(
% 1.36/0.56    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 1.36/0.56    inference(cnf_transformation,[],[f7])).
% 1.36/0.56  fof(f7,axiom,(
% 1.36/0.56    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 1.36/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 1.36/0.56  fof(f42,plain,(
% 1.36/0.56    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X2))) )),
% 1.36/0.56    inference(definition_unfolding,[],[f35,f27,f27,f27])).
% 1.36/0.56  fof(f35,plain,(
% 1.36/0.56    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 1.36/0.56    inference(cnf_transformation,[],[f9])).
% 1.36/0.56  fof(f9,axiom,(
% 1.36/0.56    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 1.36/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).
% 1.36/0.56  fof(f96,plain,(
% 1.36/0.56    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.36/0.56    inference(unit_resulting_resolution,[],[f38,f40])).
% 1.36/0.56  fof(f40,plain,(
% 1.36/0.56    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) | r1_tarski(X0,X1)) )),
% 1.36/0.56    inference(definition_unfolding,[],[f31,f27])).
% 1.36/0.56  fof(f31,plain,(
% 1.36/0.56    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 1.36/0.56    inference(cnf_transformation,[],[f21])).
% 1.36/0.56  fof(f21,plain,(
% 1.36/0.56    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 1.36/0.56    inference(nnf_transformation,[],[f2])).
% 1.36/0.56  fof(f2,axiom,(
% 1.36/0.56    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 1.36/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.36/0.56  fof(f2360,plain,(
% 1.36/0.56    ( ! [X3] : (k2_xboole_0(k5_xboole_0(X3,k3_xboole_0(X3,X3)),X3) = X3) ) | ~spl3_4),
% 1.36/0.56    inference(superposition,[],[f168,f190])).
% 1.36/0.56  fof(f190,plain,(
% 1.36/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 1.36/0.56    inference(unit_resulting_resolution,[],[f96,f28])).
% 1.36/0.56  fof(f2171,plain,(
% 1.36/0.56    ( ! [X1] : (k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X1)) = k5_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,X1)))) ) | ~spl3_20),
% 1.36/0.56    inference(forward_demodulation,[],[f590,f2062])).
% 1.36/0.56  fof(f2062,plain,(
% 1.36/0.56    ( ! [X6] : (k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,X6))) = k5_xboole_0(sK0,k3_xboole_0(sK0,X6))) ) | ~spl3_20),
% 1.36/0.56    inference(forward_demodulation,[],[f578,f572])).
% 1.36/0.56  fof(f572,plain,(
% 1.36/0.56    ( ! [X0] : (k3_xboole_0(sK0,X0) = k3_xboole_0(sK0,k3_xboole_0(sK1,X0))) ) | ~spl3_20),
% 1.36/0.56    inference(superposition,[],[f34,f545])).
% 1.36/0.56  fof(f545,plain,(
% 1.36/0.56    sK0 = k3_xboole_0(sK0,sK1) | ~spl3_20),
% 1.36/0.56    inference(avatar_component_clause,[],[f543])).
% 1.36/0.56  fof(f578,plain,(
% 1.36/0.56    ( ! [X6] : (k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,X6))) = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(sK1,X6)))) ) | ~spl3_20),
% 1.36/0.56    inference(superposition,[],[f118,f545])).
% 1.36/0.56  fof(f590,plain,(
% 1.36/0.56    ( ! [X1] : (k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,X1)))) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X1))) ) | ~spl3_20),
% 1.36/0.56    inference(forward_demodulation,[],[f574,f24])).
% 1.36/0.56  fof(f574,plain,(
% 1.36/0.56    ( ! [X1] : (k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,X1)))) = k2_xboole_0(k5_xboole_0(sK0,sK0),k3_xboole_0(sK0,X1))) ) | ~spl3_20),
% 1.36/0.56    inference(superposition,[],[f42,f545])).
% 1.36/0.56  fof(f3029,plain,(
% 1.36/0.56    spl3_31 | ~spl3_4 | ~spl3_20),
% 1.36/0.56    inference(avatar_split_clause,[],[f3004,f543,f60,f2147])).
% 1.36/0.56  fof(f3004,plain,(
% 1.36/0.56    sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) | (~spl3_4 | ~spl3_20)),
% 1.36/0.56    inference(superposition,[],[f2996,f437])).
% 1.36/0.56  fof(f437,plain,(
% 1.36/0.56    ( ! [X10,X8,X11,X9] : (k5_xboole_0(X8,k3_xboole_0(X8,k3_xboole_0(X9,k5_xboole_0(X10,k3_xboole_0(X10,k2_xboole_0(k3_xboole_0(X9,X10),X11)))))) = X8) ) | ~spl3_4),
% 1.36/0.56    inference(superposition,[],[f164,f168])).
% 1.36/0.56  fof(f164,plain,(
% 1.36/0.56    ( ! [X4,X2,X3,X1] : (k2_xboole_0(k5_xboole_0(X4,k3_xboole_0(X4,k3_xboole_0(X1,X2))),k3_xboole_0(X4,X3)) = k5_xboole_0(X4,k3_xboole_0(X4,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))))) )),
% 1.36/0.56    inference(forward_demodulation,[],[f151,f118])).
% 1.36/0.56  fof(f151,plain,(
% 1.36/0.56    ( ! [X4,X2,X3,X1] : (k2_xboole_0(k5_xboole_0(X4,k3_xboole_0(X4,k3_xboole_0(X1,X2))),k3_xboole_0(X4,X3)) = k5_xboole_0(X4,k3_xboole_0(X4,k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X2,X3)))))) )),
% 1.36/0.56    inference(superposition,[],[f42,f34])).
% 1.36/0.56  fof(f2996,plain,(
% 1.36/0.56    ( ! [X0] : (sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK2,k3_xboole_0(sK2,X0))))) ) | (~spl3_4 | ~spl3_20)),
% 1.36/0.56    inference(forward_demodulation,[],[f2995,f2198])).
% 1.36/0.56  fof(f2198,plain,(
% 1.36/0.56    ( ! [X2,X3] : (k2_xboole_0(X2,k3_xboole_0(X2,X3)) = X2) ) | ~spl3_4),
% 1.36/0.56    inference(forward_demodulation,[],[f2197,f25])).
% 1.36/0.56  fof(f2197,plain,(
% 1.36/0.56    ( ! [X2,X3] : (k5_xboole_0(X2,k1_xboole_0) = k2_xboole_0(X2,k3_xboole_0(X2,X3))) ) | ~spl3_4),
% 1.36/0.56    inference(forward_demodulation,[],[f2196,f133])).
% 1.36/0.56  fof(f2196,plain,(
% 1.36/0.56    ( ! [X2,X3] : (k5_xboole_0(X2,k3_xboole_0(X2,k1_xboole_0)) = k2_xboole_0(X2,k3_xboole_0(X2,X3))) ) | ~spl3_4),
% 1.36/0.56    inference(forward_demodulation,[],[f2195,f24])).
% 1.36/0.56  fof(f2195,plain,(
% 1.36/0.56    ( ! [X2,X3] : (k2_xboole_0(X2,k3_xboole_0(X2,X3)) = k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(k1_xboole_0,k1_xboole_0)))) ) | ~spl3_4),
% 1.36/0.56    inference(forward_demodulation,[],[f922,f567])).
% 1.36/0.56  fof(f567,plain,(
% 1.36/0.56    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) ) | ~spl3_4),
% 1.36/0.56    inference(unit_resulting_resolution,[],[f514,f28])).
% 1.36/0.56  fof(f514,plain,(
% 1.36/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl3_4),
% 1.36/0.56    inference(superposition,[],[f209,f38])).
% 1.36/0.56  fof(f922,plain,(
% 1.36/0.56    ( ! [X2,X3] : (k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X3)))) = k2_xboole_0(X2,k3_xboole_0(X2,X3))) ) | ~spl3_4),
% 1.36/0.56    inference(forward_demodulation,[],[f861,f168])).
% 1.36/0.56  fof(f861,plain,(
% 1.36/0.56    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k2_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X0)),k3_xboole_0(X2,k2_xboole_0(X0,X1))),k3_xboole_0(X2,X3)) = k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X3))))) )),
% 1.36/0.56    inference(superposition,[],[f158,f38])).
% 1.36/0.56  fof(f158,plain,(
% 1.36/0.56    ( ! [X6,X4,X5,X3] : (k5_xboole_0(X3,k3_xboole_0(X3,k5_xboole_0(k5_xboole_0(X4,k3_xboole_0(X4,X5)),k3_xboole_0(k5_xboole_0(X4,k3_xboole_0(X4,X5)),X6)))) = k2_xboole_0(k2_xboole_0(k5_xboole_0(X3,k3_xboole_0(X3,X4)),k3_xboole_0(X3,X5)),k3_xboole_0(X3,X6))) )),
% 1.36/0.56    inference(superposition,[],[f42,f42])).
% 1.36/0.56  fof(f2995,plain,(
% 1.36/0.56    ( ! [X0] : (k2_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(sK1,X0))) = k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK2,k3_xboole_0(sK2,X0))))) ) | (~spl3_4 | ~spl3_20)),
% 1.36/0.56    inference(forward_demodulation,[],[f823,f572])).
% 1.36/0.56  fof(f823,plain,(
% 1.36/0.56    ( ! [X0] : (k2_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(sK1,X0))) = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK2,X0)))))) ) | (~spl3_4 | ~spl3_20)),
% 1.36/0.56    inference(forward_demodulation,[],[f783,f545])).
% 1.36/0.56  fof(f783,plain,(
% 1.36/0.56    ( ! [X0] : (k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK2,X0))))) = k2_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(sK1,X0)))) ) | ~spl3_4),
% 1.36/0.56    inference(superposition,[],[f171,f62])).
% 1.36/0.56  fof(f171,plain,(
% 1.36/0.56    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))))) = k2_xboole_0(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),k3_xboole_0(X0,k3_xboole_0(X1,X3)))) )),
% 1.36/0.56    inference(forward_demodulation,[],[f170,f118])).
% 1.36/0.56  fof(f170,plain,(
% 1.36/0.56    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))))) = k2_xboole_0(k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2))),k3_xboole_0(X0,k3_xboole_0(X1,X3)))) )),
% 1.36/0.56    inference(forward_demodulation,[],[f169,f34])).
% 1.36/0.56  fof(f169,plain,(
% 1.36/0.56    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))))) = k2_xboole_0(k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)),k3_xboole_0(X0,k3_xboole_0(X1,X3)))) )),
% 1.36/0.56    inference(forward_demodulation,[],[f155,f34])).
% 1.36/0.56  fof(f155,plain,(
% 1.36/0.56    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)),k3_xboole_0(k3_xboole_0(X0,X1),X3)) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))))) )),
% 1.36/0.56    inference(superposition,[],[f42,f34])).
% 1.36/0.56  fof(f554,plain,(
% 1.36/0.56    spl3_20 | ~spl3_1),
% 1.36/0.56    inference(avatar_split_clause,[],[f541,f44,f543])).
% 1.36/0.56  fof(f44,plain,(
% 1.36/0.56    spl3_1 <=> r1_tarski(sK0,sK1)),
% 1.36/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.36/0.56  fof(f541,plain,(
% 1.36/0.56    sK0 = k3_xboole_0(sK0,sK1) | ~spl3_1),
% 1.36/0.56    inference(resolution,[],[f45,f28])).
% 1.36/0.56  fof(f45,plain,(
% 1.36/0.56    r1_tarski(sK0,sK1) | ~spl3_1),
% 1.36/0.56    inference(avatar_component_clause,[],[f44])).
% 1.36/0.56  fof(f533,plain,(
% 1.36/0.56    spl3_1 | ~spl3_3 | ~spl3_4),
% 1.36/0.56    inference(avatar_split_clause,[],[f498,f60,f53,f44])).
% 1.36/0.56  fof(f53,plain,(
% 1.36/0.56    spl3_3 <=> r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 1.36/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.36/0.56  fof(f498,plain,(
% 1.36/0.56    r1_tarski(sK0,sK1) | (~spl3_3 | ~spl3_4)),
% 1.36/0.56    inference(unit_resulting_resolution,[],[f55,f209,f36])).
% 1.36/0.56  fof(f36,plain,(
% 1.36/0.56    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 1.36/0.56    inference(cnf_transformation,[],[f17])).
% 1.36/0.56  fof(f17,plain,(
% 1.36/0.56    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.36/0.56    inference(flattening,[],[f16])).
% 1.36/0.56  fof(f16,plain,(
% 1.36/0.56    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.36/0.56    inference(ennf_transformation,[],[f5])).
% 1.36/0.56  fof(f5,axiom,(
% 1.36/0.56    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.36/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.36/0.56  fof(f55,plain,(
% 1.36/0.56    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) | ~spl3_3),
% 1.36/0.56    inference(avatar_component_clause,[],[f53])).
% 1.36/0.56  fof(f71,plain,(
% 1.36/0.56    ~spl3_5 | spl3_2),
% 1.36/0.56    inference(avatar_split_clause,[],[f65,f48,f68])).
% 1.36/0.56  fof(f48,plain,(
% 1.36/0.56    spl3_2 <=> r1_xboole_0(sK0,sK2)),
% 1.36/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.36/0.56  fof(f65,plain,(
% 1.36/0.56    k1_xboole_0 != k3_xboole_0(sK0,sK2) | spl3_2),
% 1.36/0.56    inference(unit_resulting_resolution,[],[f50,f30])).
% 1.36/0.56  fof(f30,plain,(
% 1.36/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 1.36/0.56    inference(cnf_transformation,[],[f20])).
% 1.36/0.56  fof(f20,plain,(
% 1.36/0.56    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.36/0.56    inference(nnf_transformation,[],[f1])).
% 1.36/0.56  fof(f1,axiom,(
% 1.36/0.56    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.36/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.36/0.56  fof(f50,plain,(
% 1.36/0.56    ~r1_xboole_0(sK0,sK2) | spl3_2),
% 1.36/0.56    inference(avatar_component_clause,[],[f48])).
% 1.36/0.56  fof(f64,plain,(
% 1.36/0.56    spl3_4 | ~spl3_3),
% 1.36/0.56    inference(avatar_split_clause,[],[f58,f53,f60])).
% 1.36/0.56  fof(f58,plain,(
% 1.36/0.56    sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) | ~spl3_3),
% 1.36/0.56    inference(resolution,[],[f28,f55])).
% 1.36/0.56  fof(f56,plain,(
% 1.36/0.56    spl3_3),
% 1.36/0.56    inference(avatar_split_clause,[],[f37,f53])).
% 1.36/0.56  fof(f37,plain,(
% 1.36/0.56    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 1.36/0.56    inference(definition_unfolding,[],[f22,f27])).
% 1.36/0.56  fof(f22,plain,(
% 1.36/0.56    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 1.36/0.56    inference(cnf_transformation,[],[f19])).
% 1.36/0.56  fof(f19,plain,(
% 1.36/0.56    (~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 1.36/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f18])).
% 1.36/0.56  fof(f18,plain,(
% 1.36/0.56    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2)))),
% 1.36/0.56    introduced(choice_axiom,[])).
% 1.36/0.56  fof(f14,plain,(
% 1.36/0.56    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 1.36/0.56    inference(ennf_transformation,[],[f13])).
% 1.36/0.56  fof(f13,negated_conjecture,(
% 1.36/0.56    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 1.36/0.56    inference(negated_conjecture,[],[f12])).
% 1.36/0.56  fof(f12,conjecture,(
% 1.36/0.56    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 1.36/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 1.36/0.56  fof(f51,plain,(
% 1.36/0.56    ~spl3_1 | ~spl3_2),
% 1.36/0.56    inference(avatar_split_clause,[],[f23,f48,f44])).
% 1.36/0.56  fof(f23,plain,(
% 1.36/0.56    ~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)),
% 1.36/0.56    inference(cnf_transformation,[],[f19])).
% 1.36/0.56  % SZS output end Proof for theBenchmark
% 1.36/0.56  % (24296)------------------------------
% 1.36/0.56  % (24296)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.56  % (24296)Termination reason: Refutation
% 1.36/0.56  
% 1.36/0.56  % (24296)Memory used [KB]: 8571
% 1.36/0.56  % (24296)Time elapsed: 0.150 s
% 1.36/0.56  % (24296)------------------------------
% 1.36/0.56  % (24296)------------------------------
% 1.36/0.56  % (24289)Success in time 0.199 s
%------------------------------------------------------------------------------
