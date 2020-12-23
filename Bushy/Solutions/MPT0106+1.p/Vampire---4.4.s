%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : xboole_1__t99_xboole_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:36 EDT 2019

% Result     : Theorem 4.12s
% Output     : Refutation 4.12s
% Verified   : 
% Statistics : Number of formulae       :   22 (  25 expanded)
%              Number of leaves         :    6 (   8 expanded)
%              Depth                    :    8
%              Number of atoms          :   28 (  32 expanded)
%              Number of equality atoms :   19 (  22 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f102715,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f238,f102683])).

fof(f102683,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f102682])).

fof(f102682,plain,
    ( $false
    | ~ spl3_1 ),
    inference(trivial_inequality_removal,[],[f102681])).

fof(f102681,plain,
    ( k4_xboole_0(k5_xboole_0(sK0,sK1),sK2) != k4_xboole_0(k5_xboole_0(sK0,sK1),sK2)
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f102578,f20])).

fof(f20,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t99_xboole_1.p',d6_xboole_0)).

fof(f102578,plain,
    ( k4_xboole_0(k5_xboole_0(sK0,sK1),sK2) != k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2)
    | ~ spl3_1 ),
    inference(superposition,[],[f237,f8810])).

fof(f8810,plain,(
    ! [X282,X285,X281,X283,X284] : k4_xboole_0(k2_xboole_0(k4_xboole_0(X284,X285),k4_xboole_0(X281,X282)),X283) = k2_xboole_0(k4_xboole_0(X284,k2_xboole_0(X285,X283)),k4_xboole_0(X281,k2_xboole_0(X282,X283))) ),
    inference(superposition,[],[f61,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t99_xboole_1.p',t41_xboole_1)).

fof(f61,plain,(
    ! [X4,X2,X5,X3] : k4_xboole_0(k2_xboole_0(k4_xboole_0(X2,X3),X5),X4) = k2_xboole_0(k4_xboole_0(X2,k2_xboole_0(X3,X4)),k4_xboole_0(X5,X4)) ),
    inference(superposition,[],[f22,f21])).

fof(f22,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t99_xboole_1.p',t42_xboole_1)).

fof(f237,plain,
    ( k4_xboole_0(k5_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k2_xboole_0(sK0,sK2)))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f236])).

fof(f236,plain,
    ( spl3_1
  <=> k4_xboole_0(k5_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k2_xboole_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f238,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f16,f236])).

fof(f16,plain,(
    k4_xboole_0(k5_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k2_xboole_0(sK0,sK2))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    k4_xboole_0(k5_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k2_xboole_0(sK0,sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] : k4_xboole_0(k5_xboole_0(X0,X1),X2) != k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2)))
   => k4_xboole_0(k5_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK1,k2_xboole_0(sK0,sK2))) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] : k4_xboole_0(k5_xboole_0(X0,X1),X2) != k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2))) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] : k4_xboole_0(k5_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2))) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] : k4_xboole_0(k5_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2))) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t99_xboole_1.p',t99_xboole_1)).
%------------------------------------------------------------------------------
