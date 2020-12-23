%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : xboole_1__t112_xboole_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:21 EDT 2019

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 112 expanded)
%              Number of leaves         :   10 (  38 expanded)
%              Depth                    :   14
%              Number of atoms          :   59 ( 125 expanded)
%              Number of equality atoms :   45 ( 108 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5826,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f44,f5795])).

fof(f5795,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f5794])).

fof(f5794,plain,
    ( $false
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f5726,f908])).

fof(f908,plain,(
    ! [X24,X23,X25] : k3_xboole_0(X25,k5_xboole_0(X23,X24)) = k3_xboole_0(X25,k5_xboole_0(X24,X23)) ),
    inference(forward_demodulation,[],[f811,f26])).

fof(f26,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t112_xboole_1.p',d6_xboole_0)).

fof(f811,plain,(
    ! [X24,X23,X25] : k3_xboole_0(X25,k5_xboole_0(X23,X24)) = k3_xboole_0(X25,k2_xboole_0(k4_xboole_0(X24,X23),k4_xboole_0(X23,X24))) ),
    inference(superposition,[],[f740,f26])).

fof(f740,plain,(
    ! [X4,X5,X3] : k3_xboole_0(X3,k2_xboole_0(X4,X5)) = k3_xboole_0(X3,k2_xboole_0(X5,X4)) ),
    inference(superposition,[],[f181,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t112_xboole_1.p',t23_xboole_1)).

fof(f181,plain,(
    ! [X6,X7,X5] : k3_xboole_0(X5,k2_xboole_0(X6,X7)) = k2_xboole_0(k3_xboole_0(X5,X7),k3_xboole_0(X5,X6)) ),
    inference(superposition,[],[f28,f23])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t112_xboole_1.p',commutativity_k2_xboole_0)).

fof(f5726,plain,
    ( k3_xboole_0(sK1,k5_xboole_0(sK0,sK2)) != k3_xboole_0(sK1,k5_xboole_0(sK2,sK0))
    | ~ spl3_3 ),
    inference(superposition,[],[f43,f4417])).

fof(f4417,plain,(
    ! [X4,X2,X3] : k3_xboole_0(X3,k5_xboole_0(X2,X4)) = k5_xboole_0(k3_xboole_0(X4,X3),k3_xboole_0(X3,X2)) ),
    inference(superposition,[],[f2528,f24])).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t112_xboole_1.p',commutativity_k3_xboole_0)).

fof(f2528,plain,(
    ! [X45,X46,X44] : k3_xboole_0(X46,k5_xboole_0(X45,X44)) = k5_xboole_0(k3_xboole_0(X44,X46),k3_xboole_0(X45,X46)) ),
    inference(forward_demodulation,[],[f2527,f2521])).

fof(f2521,plain,(
    ! [X35,X33,X34] : k3_xboole_0(X35,k5_xboole_0(X34,X33)) = k3_xboole_0(k3_xboole_0(X35,k5_xboole_0(X34,X33)),k5_xboole_0(k3_xboole_0(X33,X35),k3_xboole_0(X34,X35))) ),
    inference(forward_demodulation,[],[f2520,f26])).

fof(f2520,plain,(
    ! [X35,X33,X34] : k3_xboole_0(X35,k2_xboole_0(k4_xboole_0(X34,X33),k4_xboole_0(X33,X34))) = k3_xboole_0(k3_xboole_0(X35,k2_xboole_0(k4_xboole_0(X34,X33),k4_xboole_0(X33,X34))),k5_xboole_0(k3_xboole_0(X33,X35),k3_xboole_0(X34,X35))) ),
    inference(forward_demodulation,[],[f2435,f611])).

fof(f611,plain,(
    ! [X4,X2,X3] : k3_xboole_0(X2,k2_xboole_0(X4,X3)) = k2_xboole_0(k3_xboole_0(X4,X2),k3_xboole_0(X3,X2)) ),
    inference(superposition,[],[f173,f24])).

fof(f173,plain,(
    ! [X4,X2,X3] : k3_xboole_0(X2,k2_xboole_0(X3,X4)) = k2_xboole_0(k3_xboole_0(X3,X2),k3_xboole_0(X2,X4)) ),
    inference(superposition,[],[f28,f24])).

fof(f2435,plain,(
    ! [X35,X33,X34] : k3_xboole_0(k2_xboole_0(k3_xboole_0(k4_xboole_0(X34,X33),X35),k3_xboole_0(k4_xboole_0(X33,X34),X35)),k5_xboole_0(k3_xboole_0(X33,X35),k3_xboole_0(X34,X35))) = k2_xboole_0(k3_xboole_0(k4_xboole_0(X34,X33),X35),k3_xboole_0(k4_xboole_0(X33,X34),X35)) ),
    inference(superposition,[],[f819,f80])).

fof(f80,plain,(
    ! [X6,X8,X7] : k5_xboole_0(k3_xboole_0(X8,X7),k3_xboole_0(X6,X7)) = k2_xboole_0(k3_xboole_0(k4_xboole_0(X8,X6),X7),k3_xboole_0(k4_xboole_0(X6,X8),X7)) ),
    inference(forward_demodulation,[],[f72,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k4_xboole_0(X0,X2),X1) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k4_xboole_0(X0,X2),X1) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t112_xboole_1.p',t111_xboole_1)).

fof(f72,plain,(
    ! [X6,X8,X7] : k5_xboole_0(k3_xboole_0(X8,X7),k3_xboole_0(X6,X7)) = k2_xboole_0(k4_xboole_0(k3_xboole_0(X8,X7),k3_xboole_0(X6,X7)),k3_xboole_0(k4_xboole_0(X6,X8),X7)) ),
    inference(superposition,[],[f26,f27])).

fof(f819,plain,(
    ! [X10,X11] : k3_xboole_0(k2_xboole_0(X10,X11),k2_xboole_0(X11,X10)) = k2_xboole_0(X10,X11) ),
    inference(superposition,[],[f740,f22])).

fof(f22,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t112_xboole_1.p',idempotence_k3_xboole_0)).

fof(f2527,plain,(
    ! [X45,X46,X44] : k3_xboole_0(k3_xboole_0(X46,k5_xboole_0(X45,X44)),k5_xboole_0(k3_xboole_0(X44,X46),k3_xboole_0(X45,X46))) = k5_xboole_0(k3_xboole_0(X44,X46),k3_xboole_0(X45,X46)) ),
    inference(forward_demodulation,[],[f2526,f26])).

fof(f2526,plain,(
    ! [X45,X46,X44] : k3_xboole_0(k3_xboole_0(X46,k2_xboole_0(k4_xboole_0(X45,X44),k4_xboole_0(X44,X45))),k5_xboole_0(k3_xboole_0(X44,X46),k3_xboole_0(X45,X46))) = k5_xboole_0(k3_xboole_0(X44,X46),k3_xboole_0(X45,X46)) ),
    inference(forward_demodulation,[],[f2438,f611])).

fof(f2438,plain,(
    ! [X45,X46,X44] : k3_xboole_0(k2_xboole_0(k3_xboole_0(k4_xboole_0(X45,X44),X46),k3_xboole_0(k4_xboole_0(X44,X45),X46)),k5_xboole_0(k3_xboole_0(X44,X46),k3_xboole_0(X45,X46))) = k5_xboole_0(k3_xboole_0(X44,X46),k3_xboole_0(X45,X46)) ),
    inference(superposition,[],[f1013,f80])).

fof(f1013,plain,(
    ! [X8,X7] : k3_xboole_0(k2_xboole_0(X8,X7),k2_xboole_0(X7,X8)) = k2_xboole_0(X7,X8) ),
    inference(superposition,[],[f819,f24])).

fof(f43,plain,
    ( k3_xboole_0(sK1,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl3_3
  <=> k3_xboole_0(sK1,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f44,plain,
    ( ~ spl3_3
    | spl3_1 ),
    inference(avatar_split_clause,[],[f37,f33,f42])).

fof(f33,plain,
    ( spl3_1
  <=> k3_xboole_0(k5_xboole_0(sK0,sK2),sK1) != k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f37,plain,
    ( k3_xboole_0(sK1,k5_xboole_0(sK0,sK2)) != k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2))
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f36,f24])).

fof(f36,plain,
    ( k3_xboole_0(k5_xboole_0(sK0,sK2),sK1) != k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2))
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f34,f24])).

fof(f34,plain,
    ( k3_xboole_0(k5_xboole_0(sK0,sK2),sK1) != k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f35,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f20,f33])).

fof(f20,plain,(
    k3_xboole_0(k5_xboole_0(sK0,sK2),sK1) != k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    k3_xboole_0(k5_xboole_0(sK0,sK2),sK1) != k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] : k3_xboole_0(k5_xboole_0(X0,X2),X1) != k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1))
   => k3_xboole_0(k5_xboole_0(sK0,sK2),sK1) != k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK2,sK1)) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2] : k3_xboole_0(k5_xboole_0(X0,X2),X1) != k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] : k3_xboole_0(k5_xboole_0(X0,X2),X1) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] : k3_xboole_0(k5_xboole_0(X0,X2),X1) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t112_xboole_1.p',t112_xboole_1)).
%------------------------------------------------------------------------------
