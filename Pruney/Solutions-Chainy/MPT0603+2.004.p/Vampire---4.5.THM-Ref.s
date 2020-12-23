%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:17 EST 2020

% Result     : Theorem 4.10s
% Output     : Refutation 4.10s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 793 expanded)
%              Number of leaves         :   13 ( 216 expanded)
%              Depth                    :   28
%              Number of atoms          :  168 (1715 expanded)
%              Number of equality atoms :   93 ( 704 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18875,plain,(
    $false ),
    inference(subsumption_resolution,[],[f18846,f29])).

fof(f29,plain,(
    k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1)
    & r1_xboole_0(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f23])).

fof(f23,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1)
        & r1_xboole_0(X0,X1)
        & v1_relat_1(X2) )
   => ( k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1)
      & r1_xboole_0(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1)
      & r1_xboole_0(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1)
      & r1_xboole_0(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_xboole_0(X0,X1)
         => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_xboole_0(X0,X1)
       => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).

fof(f18846,plain,(
    k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(superposition,[],[f18776,f17038])).

fof(f17038,plain,(
    ! [X6,X5] : k7_relat_1(k7_relat_1(sK2,X5),X6) = k7_relat_1(k7_relat_1(sK2,X5),k1_relat_1(k7_relat_1(sK2,X6))) ),
    inference(forward_demodulation,[],[f17037,f7340])).

fof(f7340,plain,(
    ! [X2,X1] : k7_relat_1(k7_relat_1(sK2,X1),X2) = k7_relat_1(k7_relat_1(sK2,X1),k1_relat_1(k7_relat_1(k7_relat_1(sK2,X1),X2))) ),
    inference(forward_demodulation,[],[f362,f224])).

fof(f224,plain,(
    ! [X2,X1] : k1_relat_1(k7_relat_1(k7_relat_1(sK2,X1),X2)) = k4_xboole_0(k1_relat_1(k7_relat_1(sK2,X1)),k4_xboole_0(k1_relat_1(k7_relat_1(sK2,X1)),X2)) ),
    inference(resolution,[],[f45,f50])).

fof(f50,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK2,X0)) ),
    inference(resolution,[],[f35,f27])).

fof(f27,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k7_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0)) ) ),
    inference(definition_unfolding,[],[f36,f34])).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f362,plain,(
    ! [X2,X1] : k7_relat_1(k7_relat_1(sK2,X1),X2) = k7_relat_1(k7_relat_1(sK2,X1),k4_xboole_0(k1_relat_1(k7_relat_1(sK2,X1)),k4_xboole_0(k1_relat_1(k7_relat_1(sK2,X1)),X2))) ),
    inference(resolution,[],[f46,f50])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k7_relat_1(X1,k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0))) ) ),
    inference(definition_unfolding,[],[f37,f34])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

fof(f17037,plain,(
    ! [X6,X5] : k7_relat_1(k7_relat_1(sK2,X5),k1_relat_1(k7_relat_1(sK2,X6))) = k7_relat_1(k7_relat_1(sK2,X5),k1_relat_1(k7_relat_1(k7_relat_1(sK2,X5),X6))) ),
    inference(forward_demodulation,[],[f17036,f224])).

fof(f17036,plain,(
    ! [X6,X5] : k7_relat_1(k7_relat_1(sK2,X5),k4_xboole_0(k1_relat_1(k7_relat_1(sK2,X5)),k4_xboole_0(k1_relat_1(k7_relat_1(sK2,X5)),X6))) = k7_relat_1(k7_relat_1(sK2,X5),k1_relat_1(k7_relat_1(sK2,X6))) ),
    inference(forward_demodulation,[],[f17035,f223])).

fof(f223,plain,(
    ! [X0] : k1_relat_1(k7_relat_1(sK2,X0)) = k4_xboole_0(k1_relat_1(sK2),k4_xboole_0(k1_relat_1(sK2),X0)) ),
    inference(resolution,[],[f45,f27])).

fof(f17035,plain,(
    ! [X6,X5] : k7_relat_1(k7_relat_1(sK2,X5),k4_xboole_0(k1_relat_1(k7_relat_1(sK2,X5)),k4_xboole_0(k1_relat_1(k7_relat_1(sK2,X5)),X6))) = k7_relat_1(k7_relat_1(sK2,X5),k4_xboole_0(k1_relat_1(sK2),k4_xboole_0(k1_relat_1(sK2),X6))) ),
    inference(forward_demodulation,[],[f16931,f559])).

fof(f559,plain,(
    ! [X4,X2,X3] : k7_relat_1(k7_relat_1(sK2,X2),k4_xboole_0(X3,k4_xboole_0(X3,X4))) = k4_xboole_0(k7_relat_1(k7_relat_1(sK2,X2),X3),k4_xboole_0(k7_relat_1(k7_relat_1(sK2,X2),X3),k7_relat_1(k7_relat_1(sK2,X2),X4))) ),
    inference(resolution,[],[f49,f50])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k7_relat_1(X2,X0),k4_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1))) ) ),
    inference(definition_unfolding,[],[f42,f34,f34])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_relat_1)).

fof(f16931,plain,(
    ! [X6,X5] : k7_relat_1(k7_relat_1(sK2,X5),k4_xboole_0(k1_relat_1(k7_relat_1(sK2,X5)),k4_xboole_0(k1_relat_1(k7_relat_1(sK2,X5)),X6))) = k4_xboole_0(k7_relat_1(k7_relat_1(sK2,X5),k1_relat_1(sK2)),k4_xboole_0(k7_relat_1(k7_relat_1(sK2,X5),k1_relat_1(sK2)),k7_relat_1(k7_relat_1(sK2,X5),X6))) ),
    inference(superposition,[],[f559,f7378])).

fof(f7378,plain,(
    ! [X1] : k7_relat_1(k7_relat_1(sK2,X1),k1_relat_1(sK2)) = k7_relat_1(k7_relat_1(sK2,X1),k1_relat_1(k7_relat_1(sK2,X1))) ),
    inference(superposition,[],[f7340,f626])).

fof(f626,plain,(
    ! [X7] : k1_relat_1(k7_relat_1(sK2,X7)) = k1_relat_1(k7_relat_1(k7_relat_1(sK2,X7),k1_relat_1(sK2))) ),
    inference(forward_demodulation,[],[f612,f370])).

fof(f370,plain,(
    ! [X0] : k7_relat_1(sK2,X0) = k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X0))) ),
    inference(forward_demodulation,[],[f361,f223])).

fof(f361,plain,(
    ! [X0] : k7_relat_1(sK2,X0) = k7_relat_1(sK2,k4_xboole_0(k1_relat_1(sK2),k4_xboole_0(k1_relat_1(sK2),X0))) ),
    inference(resolution,[],[f46,f27])).

fof(f612,plain,(
    ! [X7] : k1_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X7)))) = k1_relat_1(k7_relat_1(k7_relat_1(sK2,X7),k1_relat_1(sK2))) ),
    inference(superposition,[],[f224,f249])).

fof(f249,plain,(
    ! [X1] : k1_relat_1(k7_relat_1(sK2,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,k1_relat_1(sK2))) ),
    inference(superposition,[],[f223,f44])).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f33,f34,f34])).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f18776,plain,(
    k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,sK0),k1_relat_1(k7_relat_1(sK2,sK1))) ),
    inference(subsumption_resolution,[],[f18772,f50])).

fof(f18772,plain,
    ( k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,sK0),k1_relat_1(k7_relat_1(sK2,sK1)))
    | ~ v1_relat_1(k7_relat_1(sK2,sK0)) ),
    inference(resolution,[],[f18710,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,k1_relat_1(X0))
      | k1_xboole_0 = k7_relat_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k7_relat_1(X0,X1)
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

fof(f18710,plain,(
    r1_xboole_0(k1_relat_1(k7_relat_1(sK2,sK1)),k1_relat_1(k7_relat_1(sK2,sK0))) ),
    inference(trivial_inequality_removal,[],[f18696])).

fof(f18696,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k1_relat_1(k7_relat_1(sK2,sK1)),k1_relat_1(k7_relat_1(sK2,sK0))) ),
    inference(superposition,[],[f176,f18513])).

fof(f18513,plain,(
    k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,sK1),k1_relat_1(k7_relat_1(sK2,sK0))) ),
    inference(superposition,[],[f18348,f249])).

fof(f18348,plain,(
    ! [X32] : k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,X32))) ),
    inference(forward_demodulation,[],[f18206,f202])).

fof(f202,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f44,f43])).

fof(f43,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f30,f34])).

fof(f30,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f18206,plain,(
    ! [X32] : k7_relat_1(k7_relat_1(sK2,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,X32))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k7_relat_1(k7_relat_1(sK2,sK1),X32))) ),
    inference(superposition,[],[f559,f18017])).

fof(f18017,plain,(
    k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,sK1),sK0) ),
    inference(superposition,[],[f17366,f7340])).

fof(f17366,plain,(
    ! [X101] : k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,X101),k1_relat_1(k7_relat_1(k7_relat_1(sK2,sK1),sK0))) ),
    inference(forward_demodulation,[],[f17365,f56])).

fof(f56,plain,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,X0),k1_xboole_0) ),
    inference(resolution,[],[f31,f50])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_relat_1)).

fof(f17365,plain,(
    ! [X101] : k7_relat_1(k7_relat_1(sK2,X101),k1_relat_1(k7_relat_1(k7_relat_1(sK2,sK1),sK0))) = k7_relat_1(k7_relat_1(sK2,X101),k1_xboole_0) ),
    inference(forward_demodulation,[],[f17224,f256])).

fof(f256,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f248,f55])).

fof(f55,plain,(
    k1_xboole_0 = k7_relat_1(sK2,k1_xboole_0) ),
    inference(resolution,[],[f31,f27])).

fof(f248,plain,(
    k1_xboole_0 = k1_relat_1(k7_relat_1(sK2,k1_xboole_0)) ),
    inference(superposition,[],[f223,f43])).

fof(f17224,plain,(
    ! [X101] : k7_relat_1(k7_relat_1(sK2,X101),k1_relat_1(k7_relat_1(k7_relat_1(sK2,sK1),sK0))) = k7_relat_1(k7_relat_1(sK2,X101),k1_relat_1(k1_xboole_0)) ),
    inference(superposition,[],[f17038,f2907])).

fof(f2907,plain,(
    k1_xboole_0 = k7_relat_1(sK2,k1_relat_1(k7_relat_1(k7_relat_1(sK2,sK1),sK0))) ),
    inference(subsumption_resolution,[],[f2904,f27])).

fof(f2904,plain,
    ( k1_xboole_0 = k7_relat_1(sK2,k1_relat_1(k7_relat_1(k7_relat_1(sK2,sK1),sK0)))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f2898,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_relat_1(X1),X0)
      | k1_xboole_0 = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k7_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

fof(f2898,plain,(
    r1_xboole_0(k1_relat_1(sK2),k1_relat_1(k7_relat_1(k7_relat_1(sK2,sK1),sK0))) ),
    inference(subsumption_resolution,[],[f2868,f55])).

fof(f2868,plain,
    ( k1_xboole_0 != k7_relat_1(sK2,k1_xboole_0)
    | r1_xboole_0(k1_relat_1(sK2),k1_relat_1(k7_relat_1(k7_relat_1(sK2,sK1),sK0))) ),
    inference(superposition,[],[f1149,f360])).

fof(f360,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) ),
    inference(resolution,[],[f356,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f40,f34])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f356,plain,(
    r1_xboole_0(sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f355])).

fof(f355,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK1,sK0) ),
    inference(superposition,[],[f205,f142])).

fof(f142,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f48,f28])).

fof(f28,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f205,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k4_xboole_0(X2,k4_xboole_0(X2,X1))
      | r1_xboole_0(X1,X2) ) ),
    inference(superposition,[],[f47,f44])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f41,f34])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1149,plain,(
    ! [X72,X71] :
      ( k1_xboole_0 != k7_relat_1(sK2,k4_xboole_0(X71,k4_xboole_0(X71,X72)))
      | r1_xboole_0(k1_relat_1(sK2),k1_relat_1(k7_relat_1(k7_relat_1(sK2,X71),X72))) ) ),
    inference(superposition,[],[f175,f917])).

fof(f917,plain,(
    ! [X4,X3] : k7_relat_1(sK2,k4_xboole_0(X3,k4_xboole_0(X3,X4))) = k7_relat_1(sK2,k1_relat_1(k7_relat_1(k7_relat_1(sK2,X3),X4))) ),
    inference(forward_demodulation,[],[f916,f224])).

fof(f916,plain,(
    ! [X4,X3] : k7_relat_1(sK2,k4_xboole_0(k1_relat_1(k7_relat_1(sK2,X3)),k4_xboole_0(k1_relat_1(k7_relat_1(sK2,X3)),X4))) = k7_relat_1(sK2,k4_xboole_0(X3,k4_xboole_0(X3,X4))) ),
    inference(forward_demodulation,[],[f901,f558])).

fof(f558,plain,(
    ! [X0,X1] : k7_relat_1(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k7_relat_1(sK2,X0),k4_xboole_0(k7_relat_1(sK2,X0),k7_relat_1(sK2,X1))) ),
    inference(resolution,[],[f49,f27])).

fof(f901,plain,(
    ! [X4,X3] : k7_relat_1(sK2,k4_xboole_0(k1_relat_1(k7_relat_1(sK2,X3)),k4_xboole_0(k1_relat_1(k7_relat_1(sK2,X3)),X4))) = k4_xboole_0(k7_relat_1(sK2,X3),k4_xboole_0(k7_relat_1(sK2,X3),k7_relat_1(sK2,X4))) ),
    inference(superposition,[],[f558,f370])).

fof(f175,plain,(
    ! [X0] :
      ( k1_xboole_0 != k7_relat_1(sK2,X0)
      | r1_xboole_0(k1_relat_1(sK2),X0) ) ),
    inference(resolution,[],[f38,f27])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_xboole_0 != k7_relat_1(X1,X0)
      | r1_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f176,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,X1),X2)
      | r1_xboole_0(k1_relat_1(k7_relat_1(sK2,X1)),X2) ) ),
    inference(resolution,[],[f38,f50])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:56:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.42  % (13081)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.47  % (13082)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.47  % (13079)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.48  % (13086)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.48  % (13073)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.48  % (13075)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.49  % (13071)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.49  % (13078)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.49  % (13083)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.49  % (13080)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.49  % (13076)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.49  % (13072)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.50  % (13085)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.50  % (13070)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.51  % (13074)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.52  % (13077)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.52  % (13087)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.54  % (13084)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 4.10/0.88  % (13082)Refutation found. Thanks to Tanya!
% 4.10/0.88  % SZS status Theorem for theBenchmark
% 4.10/0.88  % SZS output start Proof for theBenchmark
% 4.10/0.88  fof(f18875,plain,(
% 4.10/0.88    $false),
% 4.10/0.88    inference(subsumption_resolution,[],[f18846,f29])).
% 4.10/0.88  fof(f29,plain,(
% 4.10/0.88    k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1)),
% 4.10/0.88    inference(cnf_transformation,[],[f24])).
% 4.10/0.88  fof(f24,plain,(
% 4.10/0.88    k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1) & r1_xboole_0(sK0,sK1) & v1_relat_1(sK2)),
% 4.10/0.88    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f23])).
% 4.10/0.88  fof(f23,plain,(
% 4.10/0.88    ? [X0,X1,X2] : (k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1) & r1_xboole_0(X0,X1) & v1_relat_1(X2)) => (k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1) & r1_xboole_0(sK0,sK1) & v1_relat_1(sK2))),
% 4.10/0.88    introduced(choice_axiom,[])).
% 4.10/0.88  fof(f15,plain,(
% 4.10/0.88    ? [X0,X1,X2] : (k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1) & r1_xboole_0(X0,X1) & v1_relat_1(X2))),
% 4.10/0.88    inference(flattening,[],[f14])).
% 4.10/0.88  fof(f14,plain,(
% 4.10/0.88    ? [X0,X1,X2] : ((k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1) & r1_xboole_0(X0,X1)) & v1_relat_1(X2))),
% 4.10/0.88    inference(ennf_transformation,[],[f13])).
% 4.10/0.88  fof(f13,negated_conjecture,(
% 4.10/0.88    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 4.10/0.88    inference(negated_conjecture,[],[f12])).
% 4.10/0.88  fof(f12,conjecture,(
% 4.10/0.88    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 4.10/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).
% 4.10/0.88  fof(f18846,plain,(
% 4.10/0.88    k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,sK0),sK1)),
% 4.10/0.88    inference(superposition,[],[f18776,f17038])).
% 4.10/0.88  fof(f17038,plain,(
% 4.10/0.88    ( ! [X6,X5] : (k7_relat_1(k7_relat_1(sK2,X5),X6) = k7_relat_1(k7_relat_1(sK2,X5),k1_relat_1(k7_relat_1(sK2,X6)))) )),
% 4.10/0.88    inference(forward_demodulation,[],[f17037,f7340])).
% 4.10/0.88  fof(f7340,plain,(
% 4.10/0.88    ( ! [X2,X1] : (k7_relat_1(k7_relat_1(sK2,X1),X2) = k7_relat_1(k7_relat_1(sK2,X1),k1_relat_1(k7_relat_1(k7_relat_1(sK2,X1),X2)))) )),
% 4.10/0.88    inference(forward_demodulation,[],[f362,f224])).
% 4.10/0.88  fof(f224,plain,(
% 4.10/0.88    ( ! [X2,X1] : (k1_relat_1(k7_relat_1(k7_relat_1(sK2,X1),X2)) = k4_xboole_0(k1_relat_1(k7_relat_1(sK2,X1)),k4_xboole_0(k1_relat_1(k7_relat_1(sK2,X1)),X2))) )),
% 4.10/0.88    inference(resolution,[],[f45,f50])).
% 4.10/0.88  fof(f50,plain,(
% 4.10/0.88    ( ! [X0] : (v1_relat_1(k7_relat_1(sK2,X0))) )),
% 4.10/0.88    inference(resolution,[],[f35,f27])).
% 4.10/0.88  fof(f27,plain,(
% 4.10/0.88    v1_relat_1(sK2)),
% 4.10/0.88    inference(cnf_transformation,[],[f24])).
% 4.10/0.88  fof(f35,plain,(
% 4.10/0.88    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1))) )),
% 4.10/0.88    inference(cnf_transformation,[],[f18])).
% 4.10/0.88  fof(f18,plain,(
% 4.10/0.88    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 4.10/0.88    inference(ennf_transformation,[],[f5])).
% 4.10/0.88  fof(f5,axiom,(
% 4.10/0.88    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 4.10/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 4.10/0.88  fof(f45,plain,(
% 4.10/0.88    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0))) )),
% 4.10/0.88    inference(definition_unfolding,[],[f36,f34])).
% 4.10/0.88  fof(f34,plain,(
% 4.10/0.88    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 4.10/0.88    inference(cnf_transformation,[],[f4])).
% 4.10/0.88  fof(f4,axiom,(
% 4.10/0.88    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 4.10/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 4.10/0.88  fof(f36,plain,(
% 4.10/0.88    ( ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 4.10/0.88    inference(cnf_transformation,[],[f19])).
% 4.10/0.88  fof(f19,plain,(
% 4.10/0.88    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 4.10/0.88    inference(ennf_transformation,[],[f10])).
% 4.10/0.88  fof(f10,axiom,(
% 4.10/0.88    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)))),
% 4.10/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 4.10/0.88  fof(f362,plain,(
% 4.10/0.88    ( ! [X2,X1] : (k7_relat_1(k7_relat_1(sK2,X1),X2) = k7_relat_1(k7_relat_1(sK2,X1),k4_xboole_0(k1_relat_1(k7_relat_1(sK2,X1)),k4_xboole_0(k1_relat_1(k7_relat_1(sK2,X1)),X2)))) )),
% 4.10/0.88    inference(resolution,[],[f46,f50])).
% 4.10/0.88  fof(f46,plain,(
% 4.10/0.88    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k7_relat_1(X1,k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0)))) )),
% 4.10/0.88    inference(definition_unfolding,[],[f37,f34])).
% 4.10/0.88  fof(f37,plain,(
% 4.10/0.88    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 4.10/0.88    inference(cnf_transformation,[],[f20])).
% 4.10/0.88  fof(f20,plain,(
% 4.10/0.88    ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 4.10/0.88    inference(ennf_transformation,[],[f9])).
% 4.10/0.88  fof(f9,axiom,(
% 4.10/0.88    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 4.10/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).
% 4.10/0.88  fof(f17037,plain,(
% 4.10/0.88    ( ! [X6,X5] : (k7_relat_1(k7_relat_1(sK2,X5),k1_relat_1(k7_relat_1(sK2,X6))) = k7_relat_1(k7_relat_1(sK2,X5),k1_relat_1(k7_relat_1(k7_relat_1(sK2,X5),X6)))) )),
% 4.10/0.88    inference(forward_demodulation,[],[f17036,f224])).
% 4.10/0.88  fof(f17036,plain,(
% 4.10/0.88    ( ! [X6,X5] : (k7_relat_1(k7_relat_1(sK2,X5),k4_xboole_0(k1_relat_1(k7_relat_1(sK2,X5)),k4_xboole_0(k1_relat_1(k7_relat_1(sK2,X5)),X6))) = k7_relat_1(k7_relat_1(sK2,X5),k1_relat_1(k7_relat_1(sK2,X6)))) )),
% 4.10/0.88    inference(forward_demodulation,[],[f17035,f223])).
% 4.10/0.88  fof(f223,plain,(
% 4.10/0.88    ( ! [X0] : (k1_relat_1(k7_relat_1(sK2,X0)) = k4_xboole_0(k1_relat_1(sK2),k4_xboole_0(k1_relat_1(sK2),X0))) )),
% 4.10/0.88    inference(resolution,[],[f45,f27])).
% 4.10/0.88  fof(f17035,plain,(
% 4.10/0.88    ( ! [X6,X5] : (k7_relat_1(k7_relat_1(sK2,X5),k4_xboole_0(k1_relat_1(k7_relat_1(sK2,X5)),k4_xboole_0(k1_relat_1(k7_relat_1(sK2,X5)),X6))) = k7_relat_1(k7_relat_1(sK2,X5),k4_xboole_0(k1_relat_1(sK2),k4_xboole_0(k1_relat_1(sK2),X6)))) )),
% 4.10/0.88    inference(forward_demodulation,[],[f16931,f559])).
% 4.10/0.88  fof(f559,plain,(
% 4.10/0.88    ( ! [X4,X2,X3] : (k7_relat_1(k7_relat_1(sK2,X2),k4_xboole_0(X3,k4_xboole_0(X3,X4))) = k4_xboole_0(k7_relat_1(k7_relat_1(sK2,X2),X3),k4_xboole_0(k7_relat_1(k7_relat_1(sK2,X2),X3),k7_relat_1(k7_relat_1(sK2,X2),X4)))) )),
% 4.10/0.88    inference(resolution,[],[f49,f50])).
% 4.10/0.88  fof(f49,plain,(
% 4.10/0.88    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k7_relat_1(X2,X0),k4_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)))) )),
% 4.10/0.88    inference(definition_unfolding,[],[f42,f34,f34])).
% 4.10/0.88  fof(f42,plain,(
% 4.10/0.88    ( ! [X2,X0,X1] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 4.10/0.88    inference(cnf_transformation,[],[f22])).
% 4.10/0.88  fof(f22,plain,(
% 4.10/0.88    ! [X0,X1,X2] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 4.10/0.88    inference(ennf_transformation,[],[f6])).
% 4.10/0.88  fof(f6,axiom,(
% 4.10/0.88    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)))),
% 4.10/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_relat_1)).
% 4.10/0.88  fof(f16931,plain,(
% 4.10/0.88    ( ! [X6,X5] : (k7_relat_1(k7_relat_1(sK2,X5),k4_xboole_0(k1_relat_1(k7_relat_1(sK2,X5)),k4_xboole_0(k1_relat_1(k7_relat_1(sK2,X5)),X6))) = k4_xboole_0(k7_relat_1(k7_relat_1(sK2,X5),k1_relat_1(sK2)),k4_xboole_0(k7_relat_1(k7_relat_1(sK2,X5),k1_relat_1(sK2)),k7_relat_1(k7_relat_1(sK2,X5),X6)))) )),
% 4.10/0.88    inference(superposition,[],[f559,f7378])).
% 4.10/0.88  fof(f7378,plain,(
% 4.10/0.88    ( ! [X1] : (k7_relat_1(k7_relat_1(sK2,X1),k1_relat_1(sK2)) = k7_relat_1(k7_relat_1(sK2,X1),k1_relat_1(k7_relat_1(sK2,X1)))) )),
% 4.10/0.88    inference(superposition,[],[f7340,f626])).
% 4.10/0.88  fof(f626,plain,(
% 4.10/0.88    ( ! [X7] : (k1_relat_1(k7_relat_1(sK2,X7)) = k1_relat_1(k7_relat_1(k7_relat_1(sK2,X7),k1_relat_1(sK2)))) )),
% 4.10/0.88    inference(forward_demodulation,[],[f612,f370])).
% 4.10/0.88  fof(f370,plain,(
% 4.10/0.88    ( ! [X0] : (k7_relat_1(sK2,X0) = k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X0)))) )),
% 4.10/0.88    inference(forward_demodulation,[],[f361,f223])).
% 4.10/0.88  fof(f361,plain,(
% 4.10/0.88    ( ! [X0] : (k7_relat_1(sK2,X0) = k7_relat_1(sK2,k4_xboole_0(k1_relat_1(sK2),k4_xboole_0(k1_relat_1(sK2),X0)))) )),
% 4.10/0.88    inference(resolution,[],[f46,f27])).
% 4.10/0.88  fof(f612,plain,(
% 4.10/0.88    ( ! [X7] : (k1_relat_1(k7_relat_1(sK2,k1_relat_1(k7_relat_1(sK2,X7)))) = k1_relat_1(k7_relat_1(k7_relat_1(sK2,X7),k1_relat_1(sK2)))) )),
% 4.10/0.88    inference(superposition,[],[f224,f249])).
% 4.10/0.88  fof(f249,plain,(
% 4.10/0.88    ( ! [X1] : (k1_relat_1(k7_relat_1(sK2,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,k1_relat_1(sK2)))) )),
% 4.10/0.88    inference(superposition,[],[f223,f44])).
% 4.10/0.88  fof(f44,plain,(
% 4.10/0.88    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 4.10/0.88    inference(definition_unfolding,[],[f33,f34,f34])).
% 4.10/0.88  fof(f33,plain,(
% 4.10/0.88    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 4.10/0.88    inference(cnf_transformation,[],[f1])).
% 4.10/0.88  fof(f1,axiom,(
% 4.10/0.88    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 4.10/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 4.10/0.88  fof(f18776,plain,(
% 4.10/0.88    k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,sK0),k1_relat_1(k7_relat_1(sK2,sK1)))),
% 4.10/0.88    inference(subsumption_resolution,[],[f18772,f50])).
% 4.10/0.88  fof(f18772,plain,(
% 4.10/0.88    k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,sK0),k1_relat_1(k7_relat_1(sK2,sK1))) | ~v1_relat_1(k7_relat_1(sK2,sK0))),
% 4.10/0.88    inference(resolution,[],[f18710,f32])).
% 4.10/0.88  fof(f32,plain,(
% 4.10/0.88    ( ! [X0,X1] : (~r1_xboole_0(X1,k1_relat_1(X0)) | k1_xboole_0 = k7_relat_1(X0,X1) | ~v1_relat_1(X0)) )),
% 4.10/0.88    inference(cnf_transformation,[],[f17])).
% 4.10/0.88  fof(f17,plain,(
% 4.10/0.88    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 4.10/0.88    inference(ennf_transformation,[],[f8])).
% 4.10/0.88  fof(f8,axiom,(
% 4.10/0.88    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 4.10/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).
% 4.10/0.88  fof(f18710,plain,(
% 4.10/0.88    r1_xboole_0(k1_relat_1(k7_relat_1(sK2,sK1)),k1_relat_1(k7_relat_1(sK2,sK0)))),
% 4.10/0.88    inference(trivial_inequality_removal,[],[f18696])).
% 4.10/0.88  fof(f18696,plain,(
% 4.10/0.88    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_relat_1(k7_relat_1(sK2,sK1)),k1_relat_1(k7_relat_1(sK2,sK0)))),
% 4.10/0.88    inference(superposition,[],[f176,f18513])).
% 4.10/0.88  fof(f18513,plain,(
% 4.10/0.88    k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,sK1),k1_relat_1(k7_relat_1(sK2,sK0)))),
% 4.10/0.88    inference(superposition,[],[f18348,f249])).
% 4.10/0.88  fof(f18348,plain,(
% 4.10/0.88    ( ! [X32] : (k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,X32)))) )),
% 4.10/0.88    inference(forward_demodulation,[],[f18206,f202])).
% 4.10/0.88  fof(f202,plain,(
% 4.10/0.88    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) )),
% 4.10/0.88    inference(superposition,[],[f44,f43])).
% 4.10/0.88  fof(f43,plain,(
% 4.10/0.88    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 4.10/0.88    inference(definition_unfolding,[],[f30,f34])).
% 4.10/0.88  fof(f30,plain,(
% 4.10/0.88    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 4.10/0.88    inference(cnf_transformation,[],[f3])).
% 4.10/0.88  fof(f3,axiom,(
% 4.10/0.88    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 4.10/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 4.10/0.88  fof(f18206,plain,(
% 4.10/0.88    ( ! [X32] : (k7_relat_1(k7_relat_1(sK2,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,X32))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k7_relat_1(k7_relat_1(sK2,sK1),X32)))) )),
% 4.10/0.88    inference(superposition,[],[f559,f18017])).
% 4.10/0.88  fof(f18017,plain,(
% 4.10/0.88    k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,sK1),sK0)),
% 4.10/0.88    inference(superposition,[],[f17366,f7340])).
% 4.10/0.88  fof(f17366,plain,(
% 4.10/0.88    ( ! [X101] : (k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,X101),k1_relat_1(k7_relat_1(k7_relat_1(sK2,sK1),sK0)))) )),
% 4.10/0.88    inference(forward_demodulation,[],[f17365,f56])).
% 4.10/0.88  fof(f56,plain,(
% 4.10/0.88    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,X0),k1_xboole_0)) )),
% 4.10/0.88    inference(resolution,[],[f31,f50])).
% 4.10/0.88  fof(f31,plain,(
% 4.10/0.88    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)) )),
% 4.10/0.88    inference(cnf_transformation,[],[f16])).
% 4.10/0.88  fof(f16,plain,(
% 4.10/0.88    ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 4.10/0.88    inference(ennf_transformation,[],[f7])).
% 4.10/0.88  fof(f7,axiom,(
% 4.10/0.88    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0))),
% 4.10/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_relat_1)).
% 4.10/0.88  fof(f17365,plain,(
% 4.10/0.88    ( ! [X101] : (k7_relat_1(k7_relat_1(sK2,X101),k1_relat_1(k7_relat_1(k7_relat_1(sK2,sK1),sK0))) = k7_relat_1(k7_relat_1(sK2,X101),k1_xboole_0)) )),
% 4.10/0.88    inference(forward_demodulation,[],[f17224,f256])).
% 4.10/0.88  fof(f256,plain,(
% 4.10/0.88    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 4.10/0.88    inference(forward_demodulation,[],[f248,f55])).
% 4.10/0.88  fof(f55,plain,(
% 4.10/0.88    k1_xboole_0 = k7_relat_1(sK2,k1_xboole_0)),
% 4.10/0.88    inference(resolution,[],[f31,f27])).
% 4.10/0.88  fof(f248,plain,(
% 4.10/0.88    k1_xboole_0 = k1_relat_1(k7_relat_1(sK2,k1_xboole_0))),
% 4.10/0.88    inference(superposition,[],[f223,f43])).
% 4.10/0.88  fof(f17224,plain,(
% 4.10/0.88    ( ! [X101] : (k7_relat_1(k7_relat_1(sK2,X101),k1_relat_1(k7_relat_1(k7_relat_1(sK2,sK1),sK0))) = k7_relat_1(k7_relat_1(sK2,X101),k1_relat_1(k1_xboole_0))) )),
% 4.10/0.88    inference(superposition,[],[f17038,f2907])).
% 4.10/0.88  fof(f2907,plain,(
% 4.10/0.88    k1_xboole_0 = k7_relat_1(sK2,k1_relat_1(k7_relat_1(k7_relat_1(sK2,sK1),sK0)))),
% 4.10/0.88    inference(subsumption_resolution,[],[f2904,f27])).
% 4.10/0.88  fof(f2904,plain,(
% 4.10/0.88    k1_xboole_0 = k7_relat_1(sK2,k1_relat_1(k7_relat_1(k7_relat_1(sK2,sK1),sK0))) | ~v1_relat_1(sK2)),
% 4.10/0.88    inference(resolution,[],[f2898,f39])).
% 4.10/0.88  fof(f39,plain,(
% 4.10/0.88    ( ! [X0,X1] : (~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 4.10/0.88    inference(cnf_transformation,[],[f25])).
% 4.10/0.88  fof(f25,plain,(
% 4.10/0.88    ! [X0,X1] : (((k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 4.10/0.88    inference(nnf_transformation,[],[f21])).
% 4.10/0.88  fof(f21,plain,(
% 4.10/0.88    ! [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 4.10/0.88    inference(ennf_transformation,[],[f11])).
% 4.10/0.88  fof(f11,axiom,(
% 4.10/0.88    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 4.10/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).
% 4.10/0.88  fof(f2898,plain,(
% 4.10/0.88    r1_xboole_0(k1_relat_1(sK2),k1_relat_1(k7_relat_1(k7_relat_1(sK2,sK1),sK0)))),
% 4.10/0.88    inference(subsumption_resolution,[],[f2868,f55])).
% 4.10/0.88  fof(f2868,plain,(
% 4.10/0.88    k1_xboole_0 != k7_relat_1(sK2,k1_xboole_0) | r1_xboole_0(k1_relat_1(sK2),k1_relat_1(k7_relat_1(k7_relat_1(sK2,sK1),sK0)))),
% 4.10/0.88    inference(superposition,[],[f1149,f360])).
% 4.10/0.88  fof(f360,plain,(
% 4.10/0.88    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))),
% 4.10/0.88    inference(resolution,[],[f356,f48])).
% 4.10/0.88  fof(f48,plain,(
% 4.10/0.88    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 4.10/0.88    inference(definition_unfolding,[],[f40,f34])).
% 4.10/0.88  fof(f40,plain,(
% 4.10/0.88    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 4.10/0.88    inference(cnf_transformation,[],[f26])).
% 4.10/0.88  fof(f26,plain,(
% 4.10/0.88    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 4.10/0.88    inference(nnf_transformation,[],[f2])).
% 4.10/0.88  fof(f2,axiom,(
% 4.10/0.88    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 4.10/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 4.10/0.88  fof(f356,plain,(
% 4.10/0.88    r1_xboole_0(sK1,sK0)),
% 4.10/0.88    inference(trivial_inequality_removal,[],[f355])).
% 4.10/0.88  fof(f355,plain,(
% 4.10/0.88    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK1,sK0)),
% 4.10/0.88    inference(superposition,[],[f205,f142])).
% 4.10/0.88  fof(f142,plain,(
% 4.10/0.88    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 4.10/0.88    inference(resolution,[],[f48,f28])).
% 4.10/0.88  fof(f28,plain,(
% 4.10/0.88    r1_xboole_0(sK0,sK1)),
% 4.10/0.88    inference(cnf_transformation,[],[f24])).
% 4.10/0.88  fof(f205,plain,(
% 4.10/0.88    ( ! [X2,X1] : (k1_xboole_0 != k4_xboole_0(X2,k4_xboole_0(X2,X1)) | r1_xboole_0(X1,X2)) )),
% 4.10/0.88    inference(superposition,[],[f47,f44])).
% 4.10/0.88  fof(f47,plain,(
% 4.10/0.88    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 4.10/0.88    inference(definition_unfolding,[],[f41,f34])).
% 4.10/0.88  fof(f41,plain,(
% 4.10/0.88    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 4.10/0.88    inference(cnf_transformation,[],[f26])).
% 4.10/0.88  fof(f1149,plain,(
% 4.10/0.88    ( ! [X72,X71] : (k1_xboole_0 != k7_relat_1(sK2,k4_xboole_0(X71,k4_xboole_0(X71,X72))) | r1_xboole_0(k1_relat_1(sK2),k1_relat_1(k7_relat_1(k7_relat_1(sK2,X71),X72)))) )),
% 4.10/0.88    inference(superposition,[],[f175,f917])).
% 4.10/0.88  fof(f917,plain,(
% 4.10/0.88    ( ! [X4,X3] : (k7_relat_1(sK2,k4_xboole_0(X3,k4_xboole_0(X3,X4))) = k7_relat_1(sK2,k1_relat_1(k7_relat_1(k7_relat_1(sK2,X3),X4)))) )),
% 4.10/0.88    inference(forward_demodulation,[],[f916,f224])).
% 4.10/0.88  fof(f916,plain,(
% 4.10/0.88    ( ! [X4,X3] : (k7_relat_1(sK2,k4_xboole_0(k1_relat_1(k7_relat_1(sK2,X3)),k4_xboole_0(k1_relat_1(k7_relat_1(sK2,X3)),X4))) = k7_relat_1(sK2,k4_xboole_0(X3,k4_xboole_0(X3,X4)))) )),
% 4.10/0.88    inference(forward_demodulation,[],[f901,f558])).
% 4.10/0.88  fof(f558,plain,(
% 4.10/0.88    ( ! [X0,X1] : (k7_relat_1(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k7_relat_1(sK2,X0),k4_xboole_0(k7_relat_1(sK2,X0),k7_relat_1(sK2,X1)))) )),
% 4.10/0.88    inference(resolution,[],[f49,f27])).
% 4.10/0.88  fof(f901,plain,(
% 4.10/0.88    ( ! [X4,X3] : (k7_relat_1(sK2,k4_xboole_0(k1_relat_1(k7_relat_1(sK2,X3)),k4_xboole_0(k1_relat_1(k7_relat_1(sK2,X3)),X4))) = k4_xboole_0(k7_relat_1(sK2,X3),k4_xboole_0(k7_relat_1(sK2,X3),k7_relat_1(sK2,X4)))) )),
% 4.10/0.88    inference(superposition,[],[f558,f370])).
% 4.10/0.88  fof(f175,plain,(
% 4.10/0.88    ( ! [X0] : (k1_xboole_0 != k7_relat_1(sK2,X0) | r1_xboole_0(k1_relat_1(sK2),X0)) )),
% 4.10/0.88    inference(resolution,[],[f38,f27])).
% 4.10/0.88  fof(f38,plain,(
% 4.10/0.88    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_xboole_0 != k7_relat_1(X1,X0) | r1_xboole_0(k1_relat_1(X1),X0)) )),
% 4.10/0.88    inference(cnf_transformation,[],[f25])).
% 4.10/0.88  fof(f176,plain,(
% 4.10/0.88    ( ! [X2,X1] : (k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,X1),X2) | r1_xboole_0(k1_relat_1(k7_relat_1(sK2,X1)),X2)) )),
% 4.10/0.88    inference(resolution,[],[f38,f50])).
% 4.10/0.88  % SZS output end Proof for theBenchmark
% 4.10/0.88  % (13082)------------------------------
% 4.10/0.88  % (13082)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.10/0.88  % (13082)Termination reason: Refutation
% 4.10/0.88  
% 4.10/0.88  % (13082)Memory used [KB]: 7803
% 4.10/0.88  % (13082)Time elapsed: 0.467 s
% 4.10/0.88  % (13082)------------------------------
% 4.10/0.88  % (13082)------------------------------
% 4.10/0.88  % (13069)Success in time 0.523 s
%------------------------------------------------------------------------------
