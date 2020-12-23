%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:59 EST 2020

% Result     : Theorem 29.94s
% Output     : Refutation 29.94s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 541 expanded)
%              Number of leaves         :   22 ( 189 expanded)
%              Depth                    :   23
%              Number of atoms          :  211 ( 640 expanded)
%              Number of equality atoms :  125 ( 527 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f32827,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f89,f142,f166,f213,f352,f885,f32322,f32826])).

fof(f32826,plain,(
    spl3_12 ),
    inference(avatar_contradiction_clause,[],[f32825])).

fof(f32825,plain,
    ( $false
    | spl3_12 ),
    inference(subsumption_resolution,[],[f32824,f26])).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f32824,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k3_xboole_0(k5_xboole_0(sK0,sK2),sK0)
    | spl3_12 ),
    inference(forward_demodulation,[],[f32823,f70])).

fof(f70,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f56,f46])).

fof(f46,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f25,f23])).

fof(f23,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f25,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f56,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f30,f22])).

fof(f22,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f30,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f32823,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))),sK0)
    | spl3_12 ),
    inference(forward_demodulation,[],[f32822,f64])).

fof(f64,plain,(
    ! [X8,X7,X9] : k5_xboole_0(X7,k5_xboole_0(X8,X9)) = k5_xboole_0(X9,k5_xboole_0(X7,X8)) ),
    inference(superposition,[],[f30,f25])).

fof(f32822,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))),sK0)
    | spl3_12 ),
    inference(forward_demodulation,[],[f32821,f7875])).

fof(f7875,plain,(
    ! [X130,X131,X129] : k5_xboole_0(X131,k5_xboole_0(X129,X130)) = k5_xboole_0(X131,k5_xboole_0(X130,X129)) ),
    inference(forward_demodulation,[],[f7817,f46])).

fof(f7817,plain,(
    ! [X130,X131,X129] : k5_xboole_0(X131,k5_xboole_0(X129,X130)) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X131),k5_xboole_0(X130,X129)) ),
    inference(superposition,[],[f372,f438])).

fof(f438,plain,(
    ! [X37,X38] : k5_xboole_0(X38,X37) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X37,X38)) ),
    inference(superposition,[],[f64,f46])).

fof(f372,plain,(
    ! [X10,X8,X9] : k5_xboole_0(X9,X10) = k5_xboole_0(k5_xboole_0(X8,X9),k5_xboole_0(X8,X10)) ),
    inference(superposition,[],[f58,f70])).

fof(f58,plain,(
    ! [X6,X4,X5] : k5_xboole_0(X4,k5_xboole_0(X5,X6)) = k5_xboole_0(k5_xboole_0(X5,X4),X6) ),
    inference(superposition,[],[f30,f25])).

fof(f32821,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK2,sK1),sK1)),sK0)
    | spl3_12 ),
    inference(forward_demodulation,[],[f32820,f64])).

fof(f32820,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK2,sK1))),sK0)
    | spl3_12 ),
    inference(forward_demodulation,[],[f32819,f396])).

fof(f396,plain,(
    ! [X28,X26,X27,X25] : k5_xboole_0(X27,k5_xboole_0(X26,k5_xboole_0(X25,X28))) = k5_xboole_0(X27,k5_xboole_0(X25,k5_xboole_0(X26,X28))) ),
    inference(forward_demodulation,[],[f395,f30])).

fof(f395,plain,(
    ! [X28,X26,X27,X25] : k5_xboole_0(X27,k5_xboole_0(k5_xboole_0(X25,X26),X28)) = k5_xboole_0(X27,k5_xboole_0(X26,k5_xboole_0(X25,X28))) ),
    inference(forward_demodulation,[],[f377,f394])).

fof(f394,plain,(
    ! [X24,X23,X21,X22] : k5_xboole_0(k5_xboole_0(X22,k5_xboole_0(X21,X23)),X24) = k5_xboole_0(X23,k5_xboole_0(X21,k5_xboole_0(X22,X24))) ),
    inference(forward_demodulation,[],[f376,f30])).

fof(f376,plain,(
    ! [X24,X23,X21,X22] : k5_xboole_0(X23,k5_xboole_0(k5_xboole_0(X21,X22),X24)) = k5_xboole_0(k5_xboole_0(X22,k5_xboole_0(X21,X23)),X24) ),
    inference(superposition,[],[f58,f58])).

fof(f377,plain,(
    ! [X28,X26,X27,X25] : k5_xboole_0(X27,k5_xboole_0(k5_xboole_0(X25,X26),X28)) = k5_xboole_0(k5_xboole_0(X25,k5_xboole_0(X26,X27)),X28) ),
    inference(superposition,[],[f58,f30])).

fof(f32819,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK0,sK1))),sK0)
    | spl3_12 ),
    inference(forward_demodulation,[],[f32818,f64])).

fof(f32818,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK0,sK1),sK1)),sK0)
    | spl3_12 ),
    inference(forward_demodulation,[],[f32817,f64])).

fof(f32817,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k3_xboole_0(k5_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK2)),sK0)
    | spl3_12 ),
    inference(superposition,[],[f32321,f958])).

fof(f958,plain,(
    ! [X4,X2,X3] : k3_xboole_0(k5_xboole_0(X4,X2),X3) = k5_xboole_0(k3_xboole_0(X3,X4),k3_xboole_0(X3,X2)) ),
    inference(superposition,[],[f91,f26])).

fof(f91,plain,(
    ! [X4,X2,X3] : k3_xboole_0(k5_xboole_0(X2,X4),X3) = k5_xboole_0(k3_xboole_0(X3,X2),k3_xboole_0(X4,X3)) ),
    inference(superposition,[],[f33,f26])).

fof(f33,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

fof(f32321,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,sK2)))
    | spl3_12 ),
    inference(avatar_component_clause,[],[f32319])).

fof(f32319,plain,
    ( spl3_12
  <=> k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) = k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f32322,plain,
    ( ~ spl3_12
    | spl3_6
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f32121,f882,f349,f32319])).

fof(f349,plain,
    ( spl3_6
  <=> k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK2))))))) = k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f882,plain,
    ( spl3_7
  <=> k1_xboole_0 = k3_xboole_0(sK2,k5_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f32121,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,sK2)))
    | spl3_6
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f32120,f73])).

fof(f73,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f32,f24])).

fof(f24,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f32,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f32120,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,sK2))))
    | spl3_6
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f32119,f1170])).

fof(f1170,plain,
    ( ! [X2] : k3_xboole_0(X2,k5_xboole_0(sK1,sK2)) = k3_xboole_0(k5_xboole_0(X2,sK2),k5_xboole_0(sK1,sK2))
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f1154,f23])).

fof(f1154,plain,
    ( ! [X2] : k3_xboole_0(k5_xboole_0(X2,sK2),k5_xboole_0(sK1,sK2)) = k5_xboole_0(k3_xboole_0(X2,k5_xboole_0(sK1,sK2)),k1_xboole_0)
    | ~ spl3_7 ),
    inference(superposition,[],[f33,f884])).

fof(f884,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,k5_xboole_0(sK1,sK2))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f882])).

fof(f32119,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK0,sK2),k5_xboole_0(sK1,sK2))))
    | spl3_6 ),
    inference(forward_demodulation,[],[f32118,f10551])).

fof(f10551,plain,(
    ! [X12,X10,X11] : k3_xboole_0(X11,k3_xboole_0(X12,X10)) = k3_xboole_0(X11,k3_xboole_0(X10,X12)) ),
    inference(superposition,[],[f506,f78])).

fof(f78,plain,(
    ! [X6,X7,X5] : k3_xboole_0(X5,k3_xboole_0(X6,X7)) = k3_xboole_0(X7,k3_xboole_0(X5,X6)) ),
    inference(superposition,[],[f32,f26])).

fof(f506,plain,(
    ! [X4,X5,X3] : k3_xboole_0(X3,k3_xboole_0(X4,X5)) = k3_xboole_0(X4,k3_xboole_0(X3,X5)) ),
    inference(superposition,[],[f74,f32])).

fof(f74,plain,(
    ! [X4,X2,X3] : k3_xboole_0(X2,k3_xboole_0(X3,X4)) = k3_xboole_0(k3_xboole_0(X3,X2),X4) ),
    inference(superposition,[],[f32,f26])).

fof(f32118,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK0,sK2))))
    | spl3_6 ),
    inference(forward_demodulation,[],[f32117,f70])).

fof(f32117,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))))
    | spl3_6 ),
    inference(forward_demodulation,[],[f32116,f64])).

fof(f32116,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))))))
    | spl3_6 ),
    inference(forward_demodulation,[],[f32115,f7875])).

fof(f32115,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK2,sK1),sK1)))))
    | spl3_6 ),
    inference(forward_demodulation,[],[f32114,f64])).

fof(f32114,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK2,sK1))))))
    | spl3_6 ),
    inference(forward_demodulation,[],[f32113,f396])).

fof(f32113,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK0,sK1))))))
    | spl3_6 ),
    inference(forward_demodulation,[],[f32112,f743])).

fof(f743,plain,(
    ! [X12,X10,X11] : k5_xboole_0(X10,k5_xboole_0(X11,k3_xboole_0(X12,k5_xboole_0(X10,X11)))) = k3_xboole_0(k5_xboole_0(X10,X11),k5_xboole_0(X10,k5_xboole_0(X11,X12))) ),
    inference(forward_demodulation,[],[f715,f30])).

fof(f715,plain,(
    ! [X12,X10,X11] : k5_xboole_0(X10,k5_xboole_0(X11,k3_xboole_0(X12,k5_xboole_0(X10,X11)))) = k3_xboole_0(k5_xboole_0(X10,X11),k5_xboole_0(k5_xboole_0(X10,X11),X12)) ),
    inference(superposition,[],[f105,f30])).

fof(f105,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f90,f26])).

fof(f90,plain,(
    ! [X0,X1] : k3_xboole_0(k5_xboole_0(X0,X1),X0) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f33,f24])).

fof(f32112,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK2))))))
    | spl3_6 ),
    inference(forward_demodulation,[],[f32111,f7875])).

fof(f32111,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK2)),sK2))))
    | spl3_6 ),
    inference(forward_demodulation,[],[f32110,f64])).

fof(f32110,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK2))))))
    | spl3_6 ),
    inference(forward_demodulation,[],[f32107,f26])).

fof(f32107,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK2)))),sK0))
    | spl3_6 ),
    inference(backward_demodulation,[],[f351,f32103])).

fof(f32103,plain,(
    ! [X103,X105,X106,X104] : k3_xboole_0(X105,k5_xboole_0(X104,k5_xboole_0(X103,k3_xboole_0(X105,X106)))) = k3_xboole_0(k5_xboole_0(X103,k5_xboole_0(X104,X106)),X105) ),
    inference(forward_demodulation,[],[f31780,f30])).

fof(f31780,plain,(
    ! [X103,X105,X106,X104] : k3_xboole_0(k5_xboole_0(k5_xboole_0(X103,X104),X106),X105) = k3_xboole_0(X105,k5_xboole_0(X104,k5_xboole_0(X103,k3_xboole_0(X105,X106)))) ),
    inference(superposition,[],[f1113,f58])).

fof(f1113,plain,(
    ! [X10,X8,X9] : k3_xboole_0(X8,k5_xboole_0(X10,k3_xboole_0(X8,X9))) = k3_xboole_0(k5_xboole_0(X10,X9),X8) ),
    inference(forward_demodulation,[],[f1112,f95])).

fof(f95,plain,(
    ! [X4,X2,X3] : k3_xboole_0(k5_xboole_0(X4,X2),X3) = k5_xboole_0(k3_xboole_0(X4,X3),k3_xboole_0(X3,X2)) ),
    inference(superposition,[],[f33,f26])).

fof(f1112,plain,(
    ! [X10,X8,X9] : k5_xboole_0(k3_xboole_0(X10,X8),k3_xboole_0(X8,X9)) = k3_xboole_0(X8,k5_xboole_0(X10,k3_xboole_0(X8,X9))) ),
    inference(forward_demodulation,[],[f1065,f26])).

fof(f1065,plain,(
    ! [X10,X8,X9] : k5_xboole_0(k3_xboole_0(X10,X8),k3_xboole_0(X8,X9)) = k3_xboole_0(k5_xboole_0(X10,k3_xboole_0(X8,X9)),X8) ),
    inference(superposition,[],[f95,f73])).

fof(f351,plain,
    ( k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK2))))))) != k3_xboole_0(sK0,k5_xboole_0(sK0,sK2))
    | spl3_6 ),
    inference(avatar_component_clause,[],[f349])).

fof(f885,plain,
    ( spl3_7
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f738,f210,f882])).

fof(f210,plain,
    ( spl3_5
  <=> sK2 = k3_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f738,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,k5_xboole_0(sK1,sK2))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f737,f22])).

fof(f737,plain,
    ( k5_xboole_0(sK2,sK2) = k3_xboole_0(sK2,k5_xboole_0(sK1,sK2))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f710,f25])).

fof(f710,plain,
    ( k5_xboole_0(sK2,sK2) = k3_xboole_0(sK2,k5_xboole_0(sK2,sK1))
    | ~ spl3_5 ),
    inference(superposition,[],[f105,f212])).

fof(f212,plain,
    ( sK2 = k3_xboole_0(sK1,sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f210])).

fof(f352,plain,
    ( ~ spl3_6
    | spl3_4 ),
    inference(avatar_split_clause,[],[f267,f163,f349])).

fof(f163,plain,
    ( spl3_4
  <=> k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) = k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f267,plain,
    ( k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK2))))))) != k3_xboole_0(sK0,k5_xboole_0(sK0,sK2))
    | spl3_4 ),
    inference(forward_demodulation,[],[f266,f253])).

fof(f253,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(backward_demodulation,[],[f122,f252])).

fof(f252,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(forward_demodulation,[],[f251,f26])).

fof(f251,plain,(
    ! [X0,X1] : k3_xboole_0(k5_xboole_0(X0,X1),X0) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(forward_demodulation,[],[f241,f95])).

fof(f241,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f40,f73])).

fof(f40,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2))) ),
    inference(backward_demodulation,[],[f36,f32])).

fof(f36,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(definition_unfolding,[],[f31,f28,f28])).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f31,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f122,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(forward_demodulation,[],[f109,f73])).

fof(f109,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(superposition,[],[f40,f24])).

fof(f266,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK2)))))))
    | spl3_4 ),
    inference(forward_demodulation,[],[f265,f78])).

fof(f265,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(k5_xboole_0(sK1,sK2),sK0))))))
    | spl3_4 ),
    inference(forward_demodulation,[],[f262,f78])).

fof(f262,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)))))))
    | spl3_4 ),
    inference(backward_demodulation,[],[f165,f253])).

fof(f165,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)))))))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f163])).

fof(f213,plain,
    ( spl3_5
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f144,f86,f210])).

fof(f86,plain,
    ( spl3_2
  <=> sK2 = k3_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f144,plain,
    ( sK2 = k3_xboole_0(sK1,sK2)
    | ~ spl3_2 ),
    inference(superposition,[],[f88,f26])).

fof(f88,plain,
    ( sK2 = k3_xboole_0(sK2,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f86])).

fof(f166,plain,
    ( ~ spl3_4
    | ~ spl3_2
    | spl3_3 ),
    inference(avatar_split_clause,[],[f156,f139,f86,f163])).

fof(f139,plain,
    ( spl3_3
  <=> k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) = k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f156,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)))))))
    | ~ spl3_2
    | spl3_3 ),
    inference(forward_demodulation,[],[f154,f26])).

fof(f154,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(sK1,sK2))))))
    | ~ spl3_2
    | spl3_3 ),
    inference(backward_demodulation,[],[f141,f144])).

fof(f141,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))))))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f139])).

fof(f142,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f39,f139])).

fof(f39,plain,(
    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))))))) ),
    inference(forward_demodulation,[],[f38,f26])).

fof(f38,plain,(
    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))))))) ),
    inference(forward_demodulation,[],[f37,f30])).

fof(f37,plain,(
    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)))))) ),
    inference(backward_demodulation,[],[f35,f36])).

fof(f35,plain,(
    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))),k3_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))))) ),
    inference(definition_unfolding,[],[f21,f28,f34,f28,f28])).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f27,f28])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f21,plain,(
    k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
    & r1_tarski(sK2,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2)))
        & r1_tarski(X2,X1) )
   => ( k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
      & r1_tarski(sK2,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2)))
      & r1_tarski(X2,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X2,X1)
       => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X2,X1)
     => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_xboole_1)).

fof(f89,plain,
    ( spl3_2
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f54,f42,f86])).

fof(f42,plain,
    ( spl3_1
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f54,plain,
    ( sK2 = k3_xboole_0(sK2,sK1)
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f44,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f44,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f45,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f20,f42])).

fof(f20,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:05:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.43  % (16886)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.46  % (16869)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.46  % (16882)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.47  % (16872)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.47  % (16883)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.48  % (16877)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.48  % (16884)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.48  % (16885)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.48  % (16875)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.48  % (16880)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.48  % (16874)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.48  % (16871)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.48  % (16870)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.48  % (16876)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.49  % (16873)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.49  % (16881)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.49  % (16879)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.52  % (16878)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 4.60/1.00  % (16873)Time limit reached!
% 4.60/1.00  % (16873)------------------------------
% 4.60/1.00  % (16873)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.60/1.00  % (16873)Termination reason: Time limit
% 4.60/1.00  % (16873)Termination phase: Saturation
% 4.60/1.00  
% 4.60/1.00  % (16873)Memory used [KB]: 13304
% 4.60/1.00  % (16873)Time elapsed: 0.600 s
% 4.60/1.00  % (16873)------------------------------
% 4.60/1.00  % (16873)------------------------------
% 12.43/1.91  % (16874)Time limit reached!
% 12.43/1.91  % (16874)------------------------------
% 12.43/1.91  % (16874)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.43/1.92  % (16875)Time limit reached!
% 12.43/1.92  % (16875)------------------------------
% 12.43/1.92  % (16875)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.43/1.92  % (16875)Termination reason: Time limit
% 12.43/1.92  % (16875)Termination phase: Saturation
% 12.43/1.92  
% 12.43/1.92  % (16875)Memory used [KB]: 40425
% 12.43/1.92  % (16875)Time elapsed: 1.500 s
% 12.43/1.92  % (16875)------------------------------
% 12.43/1.92  % (16875)------------------------------
% 12.43/1.93  % (16874)Termination reason: Time limit
% 12.43/1.93  
% 12.43/1.93  % (16874)Memory used [KB]: 31214
% 12.43/1.93  % (16874)Time elapsed: 1.506 s
% 12.43/1.93  % (16874)------------------------------
% 12.43/1.93  % (16874)------------------------------
% 14.90/2.24  % (16871)Time limit reached!
% 14.90/2.24  % (16871)------------------------------
% 14.90/2.24  % (16871)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.90/2.24  % (16871)Termination reason: Time limit
% 14.90/2.24  % (16871)Termination phase: Saturation
% 14.90/2.24  
% 14.90/2.24  % (16871)Memory used [KB]: 48101
% 14.90/2.24  % (16871)Time elapsed: 1.800 s
% 14.90/2.24  % (16871)------------------------------
% 14.90/2.24  % (16871)------------------------------
% 17.98/2.61  % (16881)Time limit reached!
% 17.98/2.61  % (16881)------------------------------
% 17.98/2.61  % (16881)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.98/2.61  % (16881)Termination reason: Time limit
% 17.98/2.61  % (16881)Termination phase: Saturation
% 17.98/2.61  
% 17.98/2.61  % (16881)Memory used [KB]: 47461
% 17.98/2.61  % (16881)Time elapsed: 2.200 s
% 17.98/2.61  % (16881)------------------------------
% 17.98/2.61  % (16881)------------------------------
% 29.94/4.11  % (16884)Refutation found. Thanks to Tanya!
% 29.94/4.11  % SZS status Theorem for theBenchmark
% 29.94/4.11  % SZS output start Proof for theBenchmark
% 29.94/4.11  fof(f32827,plain,(
% 29.94/4.11    $false),
% 29.94/4.11    inference(avatar_sat_refutation,[],[f45,f89,f142,f166,f213,f352,f885,f32322,f32826])).
% 29.94/4.11  fof(f32826,plain,(
% 29.94/4.11    spl3_12),
% 29.94/4.11    inference(avatar_contradiction_clause,[],[f32825])).
% 29.94/4.11  fof(f32825,plain,(
% 29.94/4.11    $false | spl3_12),
% 29.94/4.11    inference(subsumption_resolution,[],[f32824,f26])).
% 29.94/4.11  fof(f26,plain,(
% 29.94/4.11    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 29.94/4.11    inference(cnf_transformation,[],[f1])).
% 29.94/4.11  fof(f1,axiom,(
% 29.94/4.11    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 29.94/4.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 29.94/4.11  fof(f32824,plain,(
% 29.94/4.11    k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k3_xboole_0(k5_xboole_0(sK0,sK2),sK0) | spl3_12),
% 29.94/4.11    inference(forward_demodulation,[],[f32823,f70])).
% 29.94/4.11  fof(f70,plain,(
% 29.94/4.11    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 29.94/4.11    inference(forward_demodulation,[],[f56,f46])).
% 29.94/4.11  fof(f46,plain,(
% 29.94/4.11    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 29.94/4.11    inference(superposition,[],[f25,f23])).
% 29.94/4.11  fof(f23,plain,(
% 29.94/4.11    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 29.94/4.11    inference(cnf_transformation,[],[f9])).
% 29.94/4.11  fof(f9,axiom,(
% 29.94/4.11    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 29.94/4.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 29.94/4.11  fof(f25,plain,(
% 29.94/4.11    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 29.94/4.11    inference(cnf_transformation,[],[f2])).
% 29.94/4.11  fof(f2,axiom,(
% 29.94/4.11    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 29.94/4.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 29.94/4.11  fof(f56,plain,(
% 29.94/4.11    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 29.94/4.11    inference(superposition,[],[f30,f22])).
% 29.94/4.11  fof(f22,plain,(
% 29.94/4.11    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 29.94/4.11    inference(cnf_transformation,[],[f11])).
% 29.94/4.11  fof(f11,axiom,(
% 29.94/4.11    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 29.94/4.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 29.94/4.11  fof(f30,plain,(
% 29.94/4.11    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 29.94/4.11    inference(cnf_transformation,[],[f10])).
% 29.94/4.11  fof(f10,axiom,(
% 29.94/4.11    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 29.94/4.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 29.94/4.11  fof(f32823,plain,(
% 29.94/4.11    k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))),sK0) | spl3_12),
% 29.94/4.11    inference(forward_demodulation,[],[f32822,f64])).
% 29.94/4.11  fof(f64,plain,(
% 29.94/4.11    ( ! [X8,X7,X9] : (k5_xboole_0(X7,k5_xboole_0(X8,X9)) = k5_xboole_0(X9,k5_xboole_0(X7,X8))) )),
% 29.94/4.11    inference(superposition,[],[f30,f25])).
% 29.94/4.11  fof(f32822,plain,(
% 29.94/4.11    k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1))),sK0) | spl3_12),
% 29.94/4.11    inference(forward_demodulation,[],[f32821,f7875])).
% 29.94/4.11  fof(f7875,plain,(
% 29.94/4.11    ( ! [X130,X131,X129] : (k5_xboole_0(X131,k5_xboole_0(X129,X130)) = k5_xboole_0(X131,k5_xboole_0(X130,X129))) )),
% 29.94/4.11    inference(forward_demodulation,[],[f7817,f46])).
% 29.94/4.11  fof(f7817,plain,(
% 29.94/4.11    ( ! [X130,X131,X129] : (k5_xboole_0(X131,k5_xboole_0(X129,X130)) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X131),k5_xboole_0(X130,X129))) )),
% 29.94/4.11    inference(superposition,[],[f372,f438])).
% 29.94/4.11  fof(f438,plain,(
% 29.94/4.11    ( ! [X37,X38] : (k5_xboole_0(X38,X37) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X37,X38))) )),
% 29.94/4.11    inference(superposition,[],[f64,f46])).
% 29.94/4.11  fof(f372,plain,(
% 29.94/4.11    ( ! [X10,X8,X9] : (k5_xboole_0(X9,X10) = k5_xboole_0(k5_xboole_0(X8,X9),k5_xboole_0(X8,X10))) )),
% 29.94/4.11    inference(superposition,[],[f58,f70])).
% 29.94/4.11  fof(f58,plain,(
% 29.94/4.11    ( ! [X6,X4,X5] : (k5_xboole_0(X4,k5_xboole_0(X5,X6)) = k5_xboole_0(k5_xboole_0(X5,X4),X6)) )),
% 29.94/4.11    inference(superposition,[],[f30,f25])).
% 29.94/4.11  fof(f32821,plain,(
% 29.94/4.11    k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK2,sK1),sK1)),sK0) | spl3_12),
% 29.94/4.11    inference(forward_demodulation,[],[f32820,f64])).
% 29.94/4.11  fof(f32820,plain,(
% 29.94/4.11    k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK2,sK1))),sK0) | spl3_12),
% 29.94/4.11    inference(forward_demodulation,[],[f32819,f396])).
% 29.94/4.11  fof(f396,plain,(
% 29.94/4.11    ( ! [X28,X26,X27,X25] : (k5_xboole_0(X27,k5_xboole_0(X26,k5_xboole_0(X25,X28))) = k5_xboole_0(X27,k5_xboole_0(X25,k5_xboole_0(X26,X28)))) )),
% 29.94/4.11    inference(forward_demodulation,[],[f395,f30])).
% 29.94/4.11  fof(f395,plain,(
% 29.94/4.11    ( ! [X28,X26,X27,X25] : (k5_xboole_0(X27,k5_xboole_0(k5_xboole_0(X25,X26),X28)) = k5_xboole_0(X27,k5_xboole_0(X26,k5_xboole_0(X25,X28)))) )),
% 29.94/4.11    inference(forward_demodulation,[],[f377,f394])).
% 29.94/4.11  fof(f394,plain,(
% 29.94/4.11    ( ! [X24,X23,X21,X22] : (k5_xboole_0(k5_xboole_0(X22,k5_xboole_0(X21,X23)),X24) = k5_xboole_0(X23,k5_xboole_0(X21,k5_xboole_0(X22,X24)))) )),
% 29.94/4.11    inference(forward_demodulation,[],[f376,f30])).
% 29.94/4.11  fof(f376,plain,(
% 29.94/4.11    ( ! [X24,X23,X21,X22] : (k5_xboole_0(X23,k5_xboole_0(k5_xboole_0(X21,X22),X24)) = k5_xboole_0(k5_xboole_0(X22,k5_xboole_0(X21,X23)),X24)) )),
% 29.94/4.11    inference(superposition,[],[f58,f58])).
% 29.94/4.11  fof(f377,plain,(
% 29.94/4.11    ( ! [X28,X26,X27,X25] : (k5_xboole_0(X27,k5_xboole_0(k5_xboole_0(X25,X26),X28)) = k5_xboole_0(k5_xboole_0(X25,k5_xboole_0(X26,X27)),X28)) )),
% 29.94/4.11    inference(superposition,[],[f58,f30])).
% 29.94/4.11  fof(f32819,plain,(
% 29.94/4.11    k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK0,sK1))),sK0) | spl3_12),
% 29.94/4.11    inference(forward_demodulation,[],[f32818,f64])).
% 29.94/4.11  fof(f32818,plain,(
% 29.94/4.11    k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK0,sK1),sK1)),sK0) | spl3_12),
% 29.94/4.11    inference(forward_demodulation,[],[f32817,f64])).
% 29.94/4.11  fof(f32817,plain,(
% 29.94/4.11    k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k3_xboole_0(k5_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK2)),sK0) | spl3_12),
% 29.94/4.11    inference(superposition,[],[f32321,f958])).
% 29.94/4.11  fof(f958,plain,(
% 29.94/4.11    ( ! [X4,X2,X3] : (k3_xboole_0(k5_xboole_0(X4,X2),X3) = k5_xboole_0(k3_xboole_0(X3,X4),k3_xboole_0(X3,X2))) )),
% 29.94/4.11    inference(superposition,[],[f91,f26])).
% 29.94/4.11  fof(f91,plain,(
% 29.94/4.11    ( ! [X4,X2,X3] : (k3_xboole_0(k5_xboole_0(X2,X4),X3) = k5_xboole_0(k3_xboole_0(X3,X2),k3_xboole_0(X4,X3))) )),
% 29.94/4.11    inference(superposition,[],[f33,f26])).
% 29.94/4.11  fof(f33,plain,(
% 29.94/4.11    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) )),
% 29.94/4.11    inference(cnf_transformation,[],[f5])).
% 29.94/4.11  fof(f5,axiom,(
% 29.94/4.11    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 29.94/4.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).
% 29.94/4.11  fof(f32321,plain,(
% 29.94/4.11    k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,sK2))) | spl3_12),
% 29.94/4.11    inference(avatar_component_clause,[],[f32319])).
% 29.94/4.11  fof(f32319,plain,(
% 29.94/4.11    spl3_12 <=> k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) = k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,sK2)))),
% 29.94/4.11    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 29.94/4.11  fof(f32322,plain,(
% 29.94/4.11    ~spl3_12 | spl3_6 | ~spl3_7),
% 29.94/4.11    inference(avatar_split_clause,[],[f32121,f882,f349,f32319])).
% 29.94/4.11  fof(f349,plain,(
% 29.94/4.11    spl3_6 <=> k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK2))))))) = k3_xboole_0(sK0,k5_xboole_0(sK0,sK2))),
% 29.94/4.11    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 29.94/4.11  fof(f882,plain,(
% 29.94/4.11    spl3_7 <=> k1_xboole_0 = k3_xboole_0(sK2,k5_xboole_0(sK1,sK2))),
% 29.94/4.11    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 29.94/4.11  fof(f32121,plain,(
% 29.94/4.11    k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,sK2))) | (spl3_6 | ~spl3_7)),
% 29.94/4.11    inference(forward_demodulation,[],[f32120,f73])).
% 29.94/4.11  fof(f73,plain,(
% 29.94/4.11    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 29.94/4.11    inference(superposition,[],[f32,f24])).
% 29.94/4.11  fof(f24,plain,(
% 29.94/4.11    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 29.94/4.11    inference(cnf_transformation,[],[f15])).
% 29.94/4.11  fof(f15,plain,(
% 29.94/4.11    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 29.94/4.11    inference(rectify,[],[f3])).
% 29.94/4.11  fof(f3,axiom,(
% 29.94/4.11    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 29.94/4.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 29.94/4.11  fof(f32,plain,(
% 29.94/4.11    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 29.94/4.11    inference(cnf_transformation,[],[f6])).
% 29.94/4.11  fof(f6,axiom,(
% 29.94/4.11    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 29.94/4.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).
% 29.94/4.11  fof(f32120,plain,(
% 29.94/4.11    k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,sK2)))) | (spl3_6 | ~spl3_7)),
% 29.94/4.11    inference(forward_demodulation,[],[f32119,f1170])).
% 29.94/4.11  fof(f1170,plain,(
% 29.94/4.11    ( ! [X2] : (k3_xboole_0(X2,k5_xboole_0(sK1,sK2)) = k3_xboole_0(k5_xboole_0(X2,sK2),k5_xboole_0(sK1,sK2))) ) | ~spl3_7),
% 29.94/4.11    inference(forward_demodulation,[],[f1154,f23])).
% 29.94/4.11  fof(f1154,plain,(
% 29.94/4.11    ( ! [X2] : (k3_xboole_0(k5_xboole_0(X2,sK2),k5_xboole_0(sK1,sK2)) = k5_xboole_0(k3_xboole_0(X2,k5_xboole_0(sK1,sK2)),k1_xboole_0)) ) | ~spl3_7),
% 29.94/4.11    inference(superposition,[],[f33,f884])).
% 29.94/4.11  fof(f884,plain,(
% 29.94/4.11    k1_xboole_0 = k3_xboole_0(sK2,k5_xboole_0(sK1,sK2)) | ~spl3_7),
% 29.94/4.11    inference(avatar_component_clause,[],[f882])).
% 29.94/4.11  fof(f32119,plain,(
% 29.94/4.11    k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK0,sK2),k5_xboole_0(sK1,sK2)))) | spl3_6),
% 29.94/4.11    inference(forward_demodulation,[],[f32118,f10551])).
% 29.94/4.11  fof(f10551,plain,(
% 29.94/4.11    ( ! [X12,X10,X11] : (k3_xboole_0(X11,k3_xboole_0(X12,X10)) = k3_xboole_0(X11,k3_xboole_0(X10,X12))) )),
% 29.94/4.11    inference(superposition,[],[f506,f78])).
% 29.94/4.11  fof(f78,plain,(
% 29.94/4.11    ( ! [X6,X7,X5] : (k3_xboole_0(X5,k3_xboole_0(X6,X7)) = k3_xboole_0(X7,k3_xboole_0(X5,X6))) )),
% 29.94/4.11    inference(superposition,[],[f32,f26])).
% 29.94/4.11  fof(f506,plain,(
% 29.94/4.11    ( ! [X4,X5,X3] : (k3_xboole_0(X3,k3_xboole_0(X4,X5)) = k3_xboole_0(X4,k3_xboole_0(X3,X5))) )),
% 29.94/4.11    inference(superposition,[],[f74,f32])).
% 29.94/4.11  fof(f74,plain,(
% 29.94/4.11    ( ! [X4,X2,X3] : (k3_xboole_0(X2,k3_xboole_0(X3,X4)) = k3_xboole_0(k3_xboole_0(X3,X2),X4)) )),
% 29.94/4.11    inference(superposition,[],[f32,f26])).
% 29.94/4.11  fof(f32118,plain,(
% 29.94/4.11    k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK0,sK2)))) | spl3_6),
% 29.94/4.11    inference(forward_demodulation,[],[f32117,f70])).
% 29.94/4.11  fof(f32117,plain,(
% 29.94/4.11    k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)))))) | spl3_6),
% 29.94/4.11    inference(forward_demodulation,[],[f32116,f64])).
% 29.94/4.11  fof(f32116,plain,(
% 29.94/4.11    k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)))))) | spl3_6),
% 29.94/4.11    inference(forward_demodulation,[],[f32115,f7875])).
% 29.94/4.11  fof(f32115,plain,(
% 29.94/4.11    k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK2,sK1),sK1))))) | spl3_6),
% 29.94/4.11    inference(forward_demodulation,[],[f32114,f64])).
% 29.94/4.11  fof(f32114,plain,(
% 29.94/4.11    k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK2,sK1)))))) | spl3_6),
% 29.94/4.11    inference(forward_demodulation,[],[f32113,f396])).
% 29.94/4.11  fof(f32113,plain,(
% 29.94/4.11    k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(sK0,sK1)))))) | spl3_6),
% 29.94/4.11    inference(forward_demodulation,[],[f32112,f743])).
% 29.94/4.11  fof(f743,plain,(
% 29.94/4.11    ( ! [X12,X10,X11] : (k5_xboole_0(X10,k5_xboole_0(X11,k3_xboole_0(X12,k5_xboole_0(X10,X11)))) = k3_xboole_0(k5_xboole_0(X10,X11),k5_xboole_0(X10,k5_xboole_0(X11,X12)))) )),
% 29.94/4.11    inference(forward_demodulation,[],[f715,f30])).
% 29.94/4.11  fof(f715,plain,(
% 29.94/4.11    ( ! [X12,X10,X11] : (k5_xboole_0(X10,k5_xboole_0(X11,k3_xboole_0(X12,k5_xboole_0(X10,X11)))) = k3_xboole_0(k5_xboole_0(X10,X11),k5_xboole_0(k5_xboole_0(X10,X11),X12))) )),
% 29.94/4.11    inference(superposition,[],[f105,f30])).
% 29.94/4.11  fof(f105,plain,(
% 29.94/4.11    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 29.94/4.11    inference(forward_demodulation,[],[f90,f26])).
% 29.94/4.11  fof(f90,plain,(
% 29.94/4.11    ( ! [X0,X1] : (k3_xboole_0(k5_xboole_0(X0,X1),X0) = k5_xboole_0(X0,k3_xboole_0(X1,X0))) )),
% 29.94/4.11    inference(superposition,[],[f33,f24])).
% 29.94/4.11  fof(f32112,plain,(
% 29.94/4.11    k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK2)))))) | spl3_6),
% 29.94/4.11    inference(forward_demodulation,[],[f32111,f7875])).
% 29.94/4.11  fof(f32111,plain,(
% 29.94/4.11    k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK2)),sK2)))) | spl3_6),
% 29.94/4.11    inference(forward_demodulation,[],[f32110,f64])).
% 29.94/4.11  fof(f32110,plain,(
% 29.94/4.11    k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK2)))))) | spl3_6),
% 29.94/4.11    inference(forward_demodulation,[],[f32107,f26])).
% 29.94/4.11  fof(f32107,plain,(
% 29.94/4.11    k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK2)))),sK0)) | spl3_6),
% 29.94/4.11    inference(backward_demodulation,[],[f351,f32103])).
% 29.94/4.11  fof(f32103,plain,(
% 29.94/4.11    ( ! [X103,X105,X106,X104] : (k3_xboole_0(X105,k5_xboole_0(X104,k5_xboole_0(X103,k3_xboole_0(X105,X106)))) = k3_xboole_0(k5_xboole_0(X103,k5_xboole_0(X104,X106)),X105)) )),
% 29.94/4.11    inference(forward_demodulation,[],[f31780,f30])).
% 29.94/4.11  fof(f31780,plain,(
% 29.94/4.11    ( ! [X103,X105,X106,X104] : (k3_xboole_0(k5_xboole_0(k5_xboole_0(X103,X104),X106),X105) = k3_xboole_0(X105,k5_xboole_0(X104,k5_xboole_0(X103,k3_xboole_0(X105,X106))))) )),
% 29.94/4.11    inference(superposition,[],[f1113,f58])).
% 29.94/4.11  fof(f1113,plain,(
% 29.94/4.11    ( ! [X10,X8,X9] : (k3_xboole_0(X8,k5_xboole_0(X10,k3_xboole_0(X8,X9))) = k3_xboole_0(k5_xboole_0(X10,X9),X8)) )),
% 29.94/4.11    inference(forward_demodulation,[],[f1112,f95])).
% 29.94/4.11  fof(f95,plain,(
% 29.94/4.11    ( ! [X4,X2,X3] : (k3_xboole_0(k5_xboole_0(X4,X2),X3) = k5_xboole_0(k3_xboole_0(X4,X3),k3_xboole_0(X3,X2))) )),
% 29.94/4.11    inference(superposition,[],[f33,f26])).
% 29.94/4.11  fof(f1112,plain,(
% 29.94/4.11    ( ! [X10,X8,X9] : (k5_xboole_0(k3_xboole_0(X10,X8),k3_xboole_0(X8,X9)) = k3_xboole_0(X8,k5_xboole_0(X10,k3_xboole_0(X8,X9)))) )),
% 29.94/4.11    inference(forward_demodulation,[],[f1065,f26])).
% 29.94/4.11  fof(f1065,plain,(
% 29.94/4.11    ( ! [X10,X8,X9] : (k5_xboole_0(k3_xboole_0(X10,X8),k3_xboole_0(X8,X9)) = k3_xboole_0(k5_xboole_0(X10,k3_xboole_0(X8,X9)),X8)) )),
% 29.94/4.11    inference(superposition,[],[f95,f73])).
% 29.94/4.11  fof(f351,plain,(
% 29.94/4.11    k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK2))))))) != k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) | spl3_6),
% 29.94/4.11    inference(avatar_component_clause,[],[f349])).
% 29.94/4.11  fof(f885,plain,(
% 29.94/4.11    spl3_7 | ~spl3_5),
% 29.94/4.11    inference(avatar_split_clause,[],[f738,f210,f882])).
% 29.94/4.11  fof(f210,plain,(
% 29.94/4.11    spl3_5 <=> sK2 = k3_xboole_0(sK1,sK2)),
% 29.94/4.11    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 29.94/4.11  fof(f738,plain,(
% 29.94/4.11    k1_xboole_0 = k3_xboole_0(sK2,k5_xboole_0(sK1,sK2)) | ~spl3_5),
% 29.94/4.11    inference(forward_demodulation,[],[f737,f22])).
% 29.94/4.11  fof(f737,plain,(
% 29.94/4.11    k5_xboole_0(sK2,sK2) = k3_xboole_0(sK2,k5_xboole_0(sK1,sK2)) | ~spl3_5),
% 29.94/4.11    inference(forward_demodulation,[],[f710,f25])).
% 29.94/4.11  fof(f710,plain,(
% 29.94/4.11    k5_xboole_0(sK2,sK2) = k3_xboole_0(sK2,k5_xboole_0(sK2,sK1)) | ~spl3_5),
% 29.94/4.11    inference(superposition,[],[f105,f212])).
% 29.94/4.11  fof(f212,plain,(
% 29.94/4.11    sK2 = k3_xboole_0(sK1,sK2) | ~spl3_5),
% 29.94/4.11    inference(avatar_component_clause,[],[f210])).
% 29.94/4.11  fof(f352,plain,(
% 29.94/4.11    ~spl3_6 | spl3_4),
% 29.94/4.11    inference(avatar_split_clause,[],[f267,f163,f349])).
% 29.94/4.11  fof(f163,plain,(
% 29.94/4.11    spl3_4 <=> k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) = k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)))))))),
% 29.94/4.11    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 29.94/4.11  fof(f267,plain,(
% 29.94/4.11    k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK2))))))) != k3_xboole_0(sK0,k5_xboole_0(sK0,sK2)) | spl3_4),
% 29.94/4.11    inference(forward_demodulation,[],[f266,f253])).
% 29.94/4.11  fof(f253,plain,(
% 29.94/4.11    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 29.94/4.11    inference(backward_demodulation,[],[f122,f252])).
% 29.94/4.11  fof(f252,plain,(
% 29.94/4.11    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 29.94/4.11    inference(forward_demodulation,[],[f251,f26])).
% 29.94/4.11  fof(f251,plain,(
% 29.94/4.11    ( ! [X0,X1] : (k3_xboole_0(k5_xboole_0(X0,X1),X0) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 29.94/4.11    inference(forward_demodulation,[],[f241,f95])).
% 29.94/4.11  fof(f241,plain,(
% 29.94/4.11    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(X0,X1))) )),
% 29.94/4.11    inference(superposition,[],[f40,f73])).
% 29.94/4.11  fof(f40,plain,(
% 29.94/4.11    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2)))) )),
% 29.94/4.11    inference(backward_demodulation,[],[f36,f32])).
% 29.94/4.11  fof(f36,plain,(
% 29.94/4.11    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 29.94/4.11    inference(definition_unfolding,[],[f31,f28,f28])).
% 29.94/4.11  fof(f28,plain,(
% 29.94/4.11    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 29.94/4.11    inference(cnf_transformation,[],[f4])).
% 29.94/4.11  fof(f4,axiom,(
% 29.94/4.11    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 29.94/4.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 29.94/4.11  fof(f31,plain,(
% 29.94/4.11    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 29.94/4.11    inference(cnf_transformation,[],[f8])).
% 29.94/4.11  fof(f8,axiom,(
% 29.94/4.11    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 29.94/4.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 29.94/4.11  fof(f122,plain,(
% 29.94/4.11    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 29.94/4.11    inference(forward_demodulation,[],[f109,f73])).
% 29.94/4.11  fof(f109,plain,(
% 29.94/4.11    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 29.94/4.11    inference(superposition,[],[f40,f24])).
% 29.94/4.11  fof(f266,plain,(
% 29.94/4.11    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK2))))))) | spl3_4),
% 29.94/4.11    inference(forward_demodulation,[],[f265,f78])).
% 29.94/4.11  fof(f265,plain,(
% 29.94/4.11    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(k5_xboole_0(sK1,sK2),sK0)))))) | spl3_4),
% 29.94/4.11    inference(forward_demodulation,[],[f262,f78])).
% 29.94/4.11  fof(f262,plain,(
% 29.94/4.11    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK0,k5_xboole_0(sK0,sK1))))))) | spl3_4),
% 29.94/4.11    inference(backward_demodulation,[],[f165,f253])).
% 29.94/4.11  fof(f165,plain,(
% 29.94/4.11    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))))))) | spl3_4),
% 29.94/4.11    inference(avatar_component_clause,[],[f163])).
% 29.94/4.11  fof(f213,plain,(
% 29.94/4.11    spl3_5 | ~spl3_2),
% 29.94/4.11    inference(avatar_split_clause,[],[f144,f86,f210])).
% 29.94/4.11  fof(f86,plain,(
% 29.94/4.11    spl3_2 <=> sK2 = k3_xboole_0(sK2,sK1)),
% 29.94/4.11    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 29.94/4.11  fof(f144,plain,(
% 29.94/4.11    sK2 = k3_xboole_0(sK1,sK2) | ~spl3_2),
% 29.94/4.11    inference(superposition,[],[f88,f26])).
% 29.94/4.11  fof(f88,plain,(
% 29.94/4.11    sK2 = k3_xboole_0(sK2,sK1) | ~spl3_2),
% 29.94/4.11    inference(avatar_component_clause,[],[f86])).
% 29.94/4.11  fof(f166,plain,(
% 29.94/4.11    ~spl3_4 | ~spl3_2 | spl3_3),
% 29.94/4.11    inference(avatar_split_clause,[],[f156,f139,f86,f163])).
% 29.94/4.11  fof(f139,plain,(
% 29.94/4.11    spl3_3 <=> k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) = k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))))))),
% 29.94/4.11    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 29.94/4.11  fof(f156,plain,(
% 29.94/4.11    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))))))) | (~spl3_2 | spl3_3)),
% 29.94/4.11    inference(forward_demodulation,[],[f154,f26])).
% 29.94/4.11  fof(f154,plain,(
% 29.94/4.11    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(sK1,sK2)))))) | (~spl3_2 | spl3_3)),
% 29.94/4.11    inference(backward_demodulation,[],[f141,f144])).
% 29.94/4.11  fof(f141,plain,(
% 29.94/4.11    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))))))) | spl3_3),
% 29.94/4.11    inference(avatar_component_clause,[],[f139])).
% 29.94/4.11  fof(f142,plain,(
% 29.94/4.11    ~spl3_3),
% 29.94/4.11    inference(avatar_split_clause,[],[f39,f139])).
% 29.94/4.11  fof(f39,plain,(
% 29.94/4.11    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))))))),
% 29.94/4.11    inference(forward_demodulation,[],[f38,f26])).
% 29.94/4.11  fof(f38,plain,(
% 29.94/4.11    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)))))))),
% 29.94/4.11    inference(forward_demodulation,[],[f37,f30])).
% 29.94/4.11  fof(f37,plain,(
% 29.94/4.11    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))))))),
% 29.94/4.11    inference(backward_demodulation,[],[f35,f36])).
% 29.94/4.11  fof(f35,plain,(
% 29.94/4.11    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))),k3_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)))))),
% 29.94/4.11    inference(definition_unfolding,[],[f21,f28,f34,f28,f28])).
% 29.94/4.11  fof(f34,plain,(
% 29.94/4.11    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 29.94/4.11    inference(definition_unfolding,[],[f27,f28])).
% 29.94/4.11  fof(f27,plain,(
% 29.94/4.11    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 29.94/4.11    inference(cnf_transformation,[],[f12])).
% 29.94/4.11  fof(f12,axiom,(
% 29.94/4.11    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 29.94/4.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 29.94/4.11  fof(f21,plain,(
% 29.94/4.11    k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 29.94/4.11    inference(cnf_transformation,[],[f19])).
% 29.94/4.11  fof(f19,plain,(
% 29.94/4.11    k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) & r1_tarski(sK2,sK1)),
% 29.94/4.11    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f18])).
% 29.94/4.11  fof(f18,plain,(
% 29.94/4.11    ? [X0,X1,X2] : (k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) & r1_tarski(X2,X1)) => (k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) & r1_tarski(sK2,sK1))),
% 29.94/4.11    introduced(choice_axiom,[])).
% 29.94/4.11  fof(f16,plain,(
% 29.94/4.11    ? [X0,X1,X2] : (k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) & r1_tarski(X2,X1))),
% 29.94/4.11    inference(ennf_transformation,[],[f14])).
% 29.94/4.11  fof(f14,negated_conjecture,(
% 29.94/4.11    ~! [X0,X1,X2] : (r1_tarski(X2,X1) => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))))),
% 29.94/4.11    inference(negated_conjecture,[],[f13])).
% 29.94/4.11  fof(f13,conjecture,(
% 29.94/4.11    ! [X0,X1,X2] : (r1_tarski(X2,X1) => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))))),
% 29.94/4.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_xboole_1)).
% 29.94/4.11  fof(f89,plain,(
% 29.94/4.11    spl3_2 | ~spl3_1),
% 29.94/4.11    inference(avatar_split_clause,[],[f54,f42,f86])).
% 29.94/4.11  fof(f42,plain,(
% 29.94/4.11    spl3_1 <=> r1_tarski(sK2,sK1)),
% 29.94/4.11    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 29.94/4.11  fof(f54,plain,(
% 29.94/4.11    sK2 = k3_xboole_0(sK2,sK1) | ~spl3_1),
% 29.94/4.11    inference(unit_resulting_resolution,[],[f44,f29])).
% 29.94/4.11  fof(f29,plain,(
% 29.94/4.11    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 29.94/4.11    inference(cnf_transformation,[],[f17])).
% 29.94/4.11  fof(f17,plain,(
% 29.94/4.11    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 29.94/4.11    inference(ennf_transformation,[],[f7])).
% 29.94/4.11  fof(f7,axiom,(
% 29.94/4.11    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 29.94/4.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 29.94/4.11  fof(f44,plain,(
% 29.94/4.11    r1_tarski(sK2,sK1) | ~spl3_1),
% 29.94/4.11    inference(avatar_component_clause,[],[f42])).
% 29.94/4.11  fof(f45,plain,(
% 29.94/4.11    spl3_1),
% 29.94/4.11    inference(avatar_split_clause,[],[f20,f42])).
% 29.94/4.11  fof(f20,plain,(
% 29.94/4.11    r1_tarski(sK2,sK1)),
% 29.94/4.11    inference(cnf_transformation,[],[f19])).
% 29.94/4.11  % SZS output end Proof for theBenchmark
% 29.94/4.11  % (16884)------------------------------
% 29.94/4.11  % (16884)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 29.94/4.11  % (16884)Termination reason: Refutation
% 29.94/4.11  
% 29.94/4.11  % (16884)Memory used [KB]: 93900
% 29.94/4.11  % (16884)Time elapsed: 3.662 s
% 29.94/4.11  % (16884)------------------------------
% 29.94/4.11  % (16884)------------------------------
% 29.94/4.12  % (16868)Success in time 3.767 s
%------------------------------------------------------------------------------
