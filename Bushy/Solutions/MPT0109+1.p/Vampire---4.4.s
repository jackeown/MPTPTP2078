%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : xboole_1__t102_xboole_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:19 EDT 2019

% Result     : Theorem 1.85s
% Output     : Refutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   29 (  39 expanded)
%              Number of leaves         :    8 (  14 expanded)
%              Depth                    :    6
%              Number of atoms          :   41 (  54 expanded)
%              Number of equality atoms :   25 (  35 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f29931,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f4928,f15595,f29930])).

fof(f29930,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f29929])).

fof(f29929,plain,
    ( $false
    | ~ spl3_3 ),
    inference(trivial_inequality_removal,[],[f29928])).

fof(f29928,plain,
    ( k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k5_xboole_0(sK1,sK2))
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f29927,f28])).

fof(f28,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t102_xboole_1.p',l98_xboole_1)).

fof(f29927,plain,
    ( k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k4_xboole_0(k2_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)))
    | ~ spl3_3 ),
    inference(superposition,[],[f15594,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t102_xboole_1.p',t52_xboole_1)).

fof(f15594,plain,
    ( k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f15593])).

fof(f15593,plain,
    ( spl3_3
  <=> k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f15595,plain,
    ( ~ spl3_3
    | spl3_1 ),
    inference(avatar_split_clause,[],[f4931,f4926,f15593])).

fof(f4926,plain,
    ( spl3_1
  <=> k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f4931,plain,
    ( k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f4930,f56])).

fof(f56,plain,(
    ! [X6,X7,X5] : k3_xboole_0(X5,k3_xboole_0(X6,X7)) = k3_xboole_0(X7,k3_xboole_0(X5,X6)) ),
    inference(superposition,[],[f29,f25])).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t102_xboole_1.p',commutativity_k3_xboole_0)).

fof(f29,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t102_xboole_1.p',t16_xboole_1)).

fof(f4930,plain,
    ( k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(sK1,k3_xboole_0(sK2,sK0)))
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f4929,f56])).

fof(f4929,plain,
    ( k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(sK2,k3_xboole_0(sK0,sK1)))
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f4927,f25])).

fof(f4927,plain,
    ( k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f4926])).

fof(f4928,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f21,f4926])).

fof(f21,plain,(
    k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2] : k4_xboole_0(X0,k5_xboole_0(X1,X2)) != k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k3_xboole_0(k3_xboole_0(X0,X1),X2))
   => k4_xboole_0(sK0,k5_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_xboole_0(k3_xboole_0(sK0,sK1),sK2)) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] : k4_xboole_0(X0,k5_xboole_0(X1,X2)) != k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] : k4_xboole_0(X0,k5_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k5_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t102_xboole_1.p',t102_xboole_1)).
%------------------------------------------------------------------------------
