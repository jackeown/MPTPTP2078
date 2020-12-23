%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0552+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:36 EST 2020

% Result     : Theorem 7.65s
% Output     : Refutation 7.65s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 108 expanded)
%              Number of leaves         :   15 (  35 expanded)
%              Depth                    :   13
%              Number of atoms          :   94 ( 153 expanded)
%              Number of equality atoms :   34 (  69 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10487,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f941,f945,f10477])).

fof(f10477,plain,
    ( spl9_1
    | ~ spl9_2 ),
    inference(avatar_contradiction_clause,[],[f10420])).

fof(f10420,plain,
    ( $false
    | spl9_1
    | ~ spl9_2 ),
    inference(unit_resulting_resolution,[],[f9149,f940,f7514,f903])).

fof(f903,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f829])).

fof(f829,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f828])).

fof(f828,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f75])).

fof(f75,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f7514,plain,
    ( ! [X2,X3] : r1_tarski(k9_relat_1(sK2,k3_xboole_0(X3,X2)),k9_relat_1(sK2,X2))
    | ~ spl9_2 ),
    inference(superposition,[],[f7185,f983])).

fof(f983,plain,(
    ! [X2,X1] : k2_xboole_0(X1,k3_xboole_0(X2,X1)) = X1 ),
    inference(superposition,[],[f923,f925])).

fof(f925,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f923,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f80])).

fof(f80,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f7185,plain,
    ( ! [X14,X15] : r1_tarski(k9_relat_1(sK2,X15),k9_relat_1(sK2,k2_xboole_0(X14,X15)))
    | ~ spl9_2 ),
    inference(superposition,[],[f6263,f1592])).

fof(f1592,plain,
    ( ! [X14,X15] : k9_relat_1(sK2,k2_xboole_0(X14,X15)) = k2_xboole_0(k9_relat_1(sK2,X14),k9_relat_1(sK2,X15))
    | ~ spl9_2 ),
    inference(resolution,[],[f875,f944])).

fof(f944,plain,
    ( v1_relat_1(sK2)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f943])).

fof(f943,plain,
    ( spl9_2
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f875,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f811])).

fof(f811,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f735])).

fof(f735,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t153_relat_1)).

fof(f6263,plain,(
    ! [X59,X58] : r1_tarski(X59,k2_xboole_0(X58,X59)) ),
    inference(superposition,[],[f926,f6224])).

fof(f6224,plain,(
    ! [X0,X1] : k3_xboole_0(k2_xboole_0(X1,X0),X0) = X0 ),
    inference(forward_demodulation,[],[f1825,f983])).

fof(f1825,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(k2_xboole_0(X1,X0),X0) ),
    inference(forward_demodulation,[],[f1824,f924])).

fof(f924,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f79])).

fof(f79,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f1824,plain,(
    ! [X0,X1] : k3_xboole_0(k2_xboole_0(X1,X0),X0) = k2_xboole_0(k3_xboole_0(X0,k2_xboole_0(X0,X1)),k3_xboole_0(X1,X0)) ),
    inference(forward_demodulation,[],[f1823,f910])).

fof(f910,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).

fof(f1823,plain,(
    ! [X0,X1] : k3_xboole_0(k2_xboole_0(X1,X0),X0) = k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(X0,X1)),k3_xboole_0(X1,X0)) ),
    inference(forward_demodulation,[],[f1822,f923])).

fof(f1822,plain,(
    ! [X0,X1] : k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(X0,X1)),k3_xboole_0(X1,X0)) = k3_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(forward_demodulation,[],[f1755,f925])).

fof(f1755,plain,(
    ! [X0,X1] : k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(X0,X1)),k3_xboole_0(X1,X0)) = k3_xboole_0(k2_xboole_0(X0,k3_xboole_0(X0,X1)),k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f908,f909])).

fof(f909,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f82])).

fof(f82,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_xboole_1)).

fof(f908,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) = k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0)) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) = k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_xboole_1)).

fof(f926,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f940,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))
    | spl9_1 ),
    inference(avatar_component_clause,[],[f939])).

fof(f939,plain,
    ( spl9_1
  <=> r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f9149,plain,
    ( ! [X92,X93] : r1_tarski(k9_relat_1(sK2,k3_xboole_0(X92,X93)),k9_relat_1(sK2,X92))
    | ~ spl9_2 ),
    inference(superposition,[],[f1904,f8979])).

fof(f8979,plain,(
    ! [X2,X3] : k2_xboole_0(k3_xboole_0(X2,X3),X2) = X2 ),
    inference(forward_demodulation,[],[f8978,f983])).

fof(f8978,plain,(
    ! [X2,X3] : k2_xboole_0(k3_xboole_0(X2,X3),X2) = k2_xboole_0(X2,k3_xboole_0(X3,X2)) ),
    inference(forward_demodulation,[],[f8977,f924])).

fof(f8977,plain,(
    ! [X2,X3] : k2_xboole_0(k3_xboole_0(X2,X3),X2) = k2_xboole_0(k3_xboole_0(X2,k2_xboole_0(X2,X3)),k3_xboole_0(X3,X2)) ),
    inference(forward_demodulation,[],[f8976,f1413])).

fof(f1413,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f910,f927])).

fof(f927,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f806])).

fof(f806,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f8976,plain,(
    ! [X2,X3] : k2_xboole_0(k3_xboole_0(X2,k2_xboole_0(X2,X3)),k3_xboole_0(X3,X2)) = k3_xboole_0(X2,k2_xboole_0(X3,X2)) ),
    inference(forward_demodulation,[],[f8775,f923])).

fof(f8775,plain,(
    ! [X2,X3] : k2_xboole_0(k3_xboole_0(X2,k2_xboole_0(X2,X3)),k3_xboole_0(X3,X2)) = k3_xboole_0(k2_xboole_0(X2,k3_xboole_0(X2,X3)),k2_xboole_0(X3,X2)) ),
    inference(superposition,[],[f8548,f909])).

fof(f8548,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0)) = k2_xboole_0(k3_xboole_0(X1,k2_xboole_0(X0,X2)),k3_xboole_0(X2,X0)) ),
    inference(backward_demodulation,[],[f908,f1405])).

fof(f1405,plain,(
    ! [X4,X2,X3] : k2_xboole_0(k3_xboole_0(X3,X2),k3_xboole_0(X2,X4)) = k3_xboole_0(X2,k2_xboole_0(X3,X4)) ),
    inference(superposition,[],[f910,f925])).

fof(f1904,plain,
    ( ! [X24,X23] : r1_tarski(k9_relat_1(sK2,X23),k9_relat_1(sK2,k2_xboole_0(X23,X24)))
    | ~ spl9_2 ),
    inference(superposition,[],[f964,f1592])).

fof(f964,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[],[f914,f927])).

fof(f914,plain,(
    ! [X2,X0,X1] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f87])).

fof(f87,axiom,(
    ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_xboole_1)).

fof(f945,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f865,f943])).

fof(f865,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f844])).

fof(f844,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f807,f843])).

fof(f843,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f807,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f737])).

fof(f737,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    inference(negated_conjecture,[],[f736])).

fof(f736,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_relat_1)).

fof(f941,plain,(
    ~ spl9_1 ),
    inference(avatar_split_clause,[],[f866,f939])).

fof(f866,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f844])).
%------------------------------------------------------------------------------
