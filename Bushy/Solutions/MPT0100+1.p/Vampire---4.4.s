%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : xboole_1__t93_xboole_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:35 EDT 2019

% Result     : Theorem 1.17s
% Output     : Refutation 1.17s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 100 expanded)
%              Number of leaves         :   10 (  32 expanded)
%              Depth                    :   12
%              Number of atoms          :   49 ( 106 expanded)
%              Number of equality atoms :   41 (  97 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f36192,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f36118])).

fof(f36118,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f36117])).

fof(f36117,plain,
    ( $false
    | ~ spl2_1 ),
    inference(subsumption_resolution,[],[f36046,f25])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t93_xboole_1.p',commutativity_k2_xboole_0)).

fof(f36046,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(sK1,sK0)
    | ~ spl2_1 ),
    inference(superposition,[],[f42,f7941])).

fof(f7941,plain,(
    ! [X19,X20] : k2_xboole_0(X19,X20) = k2_xboole_0(k5_xboole_0(X20,X19),k3_xboole_0(X20,X19)) ),
    inference(forward_demodulation,[],[f7810,f890])).

fof(f890,plain,(
    ! [X43,X42] : k2_xboole_0(X42,X43) = k2_xboole_0(k4_xboole_0(X43,X42),X42) ),
    inference(forward_demodulation,[],[f845,f390])).

fof(f390,plain,(
    ! [X17,X16] : k2_xboole_0(X16,X17) = k2_xboole_0(k4_xboole_0(X17,X16),k2_xboole_0(X16,X17)) ),
    inference(superposition,[],[f94,f251])).

fof(f251,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X2,k4_xboole_0(X3,X2)) ),
    inference(superposition,[],[f67,f45])).

fof(f45,plain,(
    ! [X2,X1] : k2_xboole_0(k3_xboole_0(X2,X1),k4_xboole_0(X1,X2)) = X1 ),
    inference(superposition,[],[f28,f26])).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t93_xboole_1.p',commutativity_k3_xboole_0)).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t93_xboole_1.p',t51_xboole_1)).

fof(f67,plain,(
    ! [X12,X10,X11] : k2_xboole_0(X10,X12) = k2_xboole_0(X10,k2_xboole_0(k3_xboole_0(X10,X11),X12)) ),
    inference(superposition,[],[f30,f24])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t93_xboole_1.p',t22_xboole_1)).

fof(f30,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t93_xboole_1.p',t4_xboole_1)).

fof(f94,plain,(
    ! [X2,X1] : k2_xboole_0(X2,X1) = k2_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f63,f25])).

fof(f63,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[],[f30,f22])).

fof(f22,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t93_xboole_1.p',idempotence_k2_xboole_0)).

fof(f845,plain,(
    ! [X43,X42] : k2_xboole_0(k4_xboole_0(X43,X42),X42) = k2_xboole_0(k4_xboole_0(X43,X42),k2_xboole_0(X42,X43)) ),
    inference(superposition,[],[f703,f251])).

fof(f703,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f75,f63])).

fof(f75,plain,(
    ! [X6,X7,X5] : k2_xboole_0(X5,k2_xboole_0(X6,X7)) = k2_xboole_0(X7,k2_xboole_0(X5,X6)) ),
    inference(superposition,[],[f30,f25])).

fof(f7810,plain,(
    ! [X19,X20] : k2_xboole_0(k4_xboole_0(X20,X19),X19) = k2_xboole_0(k5_xboole_0(X20,X19),k3_xboole_0(X20,X19)) ),
    inference(superposition,[],[f73,f893])).

fof(f893,plain,(
    ! [X59,X60] : k2_xboole_0(k4_xboole_0(X60,X59),k3_xboole_0(X59,X60)) = X60 ),
    inference(forward_demodulation,[],[f850,f139])).

fof(f139,plain,(
    ! [X19,X18] : k2_xboole_0(k4_xboole_0(X18,X19),X18) = X18 ),
    inference(superposition,[],[f94,f28])).

fof(f850,plain,(
    ! [X59,X60] : k2_xboole_0(k4_xboole_0(X60,X59),X60) = k2_xboole_0(k4_xboole_0(X60,X59),k3_xboole_0(X59,X60)) ),
    inference(superposition,[],[f703,f45])).

fof(f73,plain,(
    ! [X30,X28,X29] : k2_xboole_0(k5_xboole_0(X28,X29),X30) = k2_xboole_0(k4_xboole_0(X28,X29),k2_xboole_0(k4_xboole_0(X29,X28),X30)) ),
    inference(superposition,[],[f30,f29])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t93_xboole_1.p',d6_xboole_0)).

fof(f42,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl2_1
  <=> k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f43,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f21,f41])).

fof(f21,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f19])).

fof(f19,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t93_xboole_1.p',t93_xboole_1)).
%------------------------------------------------------------------------------
