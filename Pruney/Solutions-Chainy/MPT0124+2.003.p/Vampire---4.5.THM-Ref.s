%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:59 EST 2020

% Result     : Theorem 5.66s
% Output     : Refutation 5.66s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 147 expanded)
%              Number of leaves         :   16 (  46 expanded)
%              Depth                    :   15
%              Number of atoms          :  114 ( 204 expanded)
%              Number of equality atoms :   74 ( 147 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13684,plain,(
    $false ),
    inference(subsumption_resolution,[],[f13682,f27])).

fof(f27,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
    & r1_tarski(sK2,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f23])).

fof(f23,plain,
    ( ? [X0,X1,X2] :
        ( k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2)))
        & r1_tarski(X2,X1) )
   => ( k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
      & r1_tarski(sK2,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2)))
      & r1_tarski(X2,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X2,X1)
       => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X2,X1)
     => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_xboole_1)).

fof(f13682,plain,(
    ~ r1_tarski(sK2,sK1) ),
    inference(trivial_inequality_removal,[],[f13674])).

fof(f13674,plain,
    ( k4_xboole_0(sK0,sK2) != k4_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK2,sK1) ),
    inference(superposition,[],[f13670,f61])).

fof(f61,plain,(
    ! [X2,X3] :
      ( k3_xboole_0(X3,X2) = X2
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f38,f35])).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f38,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f13670,plain,(
    k4_xboole_0(sK0,sK2) != k4_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f13669,f7591])).

fof(f7591,plain,(
    ! [X152,X151,X149,X150] : r1_xboole_0(k3_xboole_0(X152,k4_xboole_0(X149,X150)),k4_xboole_0(X150,X151)) ),
    inference(subsumption_resolution,[],[f7515,f210])).

fof(f210,plain,(
    ! [X3] : k1_xboole_0 = k3_xboole_0(X3,k1_xboole_0) ),
    inference(superposition,[],[f203,f35])).

fof(f203,plain,(
    ! [X6] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X6) ),
    inference(forward_demodulation,[],[f191,f29])).

fof(f29,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f191,plain,(
    ! [X6,X5] : k1_xboole_0 = k3_xboole_0(k5_xboole_0(X5,X5),X6) ),
    inference(superposition,[],[f46,f29])).

fof(f46,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).

fof(f7515,plain,(
    ! [X152,X151,X149,X150] :
      ( k1_xboole_0 != k3_xboole_0(X152,k1_xboole_0)
      | r1_xboole_0(k3_xboole_0(X152,k4_xboole_0(X149,X150)),k4_xboole_0(X150,X151)) ) ),
    inference(superposition,[],[f170,f1261])).

fof(f1261,plain,(
    ! [X19,X20,X18] : k1_xboole_0 = k3_xboole_0(k4_xboole_0(X18,X19),k4_xboole_0(X19,X20)) ),
    inference(forward_demodulation,[],[f1235,f206])).

fof(f206,plain,(
    ! [X6] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X6) ),
    inference(backward_demodulation,[],[f113,f203])).

fof(f113,plain,(
    ! [X6] : k3_xboole_0(k1_xboole_0,X6) = k4_xboole_0(k1_xboole_0,X6) ),
    inference(superposition,[],[f37,f49])).

fof(f49,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f34,f30])).

fof(f30,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f34,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f1235,plain,(
    ! [X19,X20,X18] : k3_xboole_0(k4_xboole_0(X18,X19),k4_xboole_0(X19,X20)) = k4_xboole_0(k1_xboole_0,X20) ),
    inference(superposition,[],[f44,f1170])).

fof(f1170,plain,(
    ! [X0,X1] : k1_xboole_0 = k3_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(backward_demodulation,[],[f208,f1167])).

fof(f1167,plain,(
    ! [X6,X7] : k1_xboole_0 = k3_xboole_0(X6,k4_xboole_0(X7,X7)) ),
    inference(subsumption_resolution,[],[f1120,f31])).

fof(f31,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f1120,plain,(
    ! [X6,X7] :
      ( k1_xboole_0 = k3_xboole_0(X6,k4_xboole_0(X7,X7))
      | ~ r1_xboole_0(k4_xboole_0(X6,X7),X7) ) ),
    inference(superposition,[],[f208,f41])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f208,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X1)) = k3_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(forward_demodulation,[],[f207,f37])).

fof(f207,plain,(
    ! [X0,X1] : k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = k3_xboole_0(X0,k4_xboole_0(X1,X1)) ),
    inference(forward_demodulation,[],[f194,f44])).

fof(f194,plain,(
    ! [X0,X1] : k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = k4_xboole_0(k3_xboole_0(X0,X1),X1) ),
    inference(superposition,[],[f37,f46])).

fof(f44,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f170,plain,(
    ! [X19,X20,X18] :
      ( k1_xboole_0 != k3_xboole_0(X18,k3_xboole_0(X19,X20))
      | r1_xboole_0(k3_xboole_0(X18,X19),X20) ) ),
    inference(superposition,[],[f42,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f13669,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK2))
    | k4_xboole_0(sK0,sK2) != k4_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f13624,f35])).

fof(f13624,plain,
    ( ~ r1_xboole_0(k3_xboole_0(k4_xboole_0(sK0,sK1),sK0),k4_xboole_0(sK1,sK2))
    | k4_xboole_0(sK0,sK2) != k4_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f1533,f5477])).

fof(f5477,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK0,sK1))
    | k4_xboole_0(sK0,sK2) != k4_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(backward_demodulation,[],[f557,f5476])).

fof(f5476,plain,(
    ! [X43,X44,X42] : k4_xboole_0(X42,k3_xboole_0(X43,X44)) = k5_xboole_0(k4_xboole_0(X42,X43),k3_xboole_0(X42,k4_xboole_0(X43,X44))) ),
    inference(forward_demodulation,[],[f5475,f44])).

fof(f5475,plain,(
    ! [X43,X44,X42] : k5_xboole_0(k4_xboole_0(X42,X43),k4_xboole_0(k3_xboole_0(X42,X43),X44)) = k4_xboole_0(X42,k3_xboole_0(X43,X44)) ),
    inference(forward_demodulation,[],[f5474,f37])).

fof(f5474,plain,(
    ! [X43,X44,X42] : k5_xboole_0(k4_xboole_0(X42,X43),k4_xboole_0(k3_xboole_0(X42,X43),X44)) = k5_xboole_0(X42,k3_xboole_0(X42,k3_xboole_0(X43,X44))) ),
    inference(forward_demodulation,[],[f5430,f45])).

fof(f5430,plain,(
    ! [X43,X44,X42] : k5_xboole_0(k4_xboole_0(X42,X43),k4_xboole_0(k3_xboole_0(X42,X43),X44)) = k5_xboole_0(X42,k3_xboole_0(k3_xboole_0(X42,X43),X44)) ),
    inference(superposition,[],[f120,f285])).

fof(f285,plain,(
    ! [X6,X5] : k3_xboole_0(X5,X6) = k5_xboole_0(X5,k4_xboole_0(X5,X6)) ),
    inference(superposition,[],[f137,f37])).

fof(f137,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f117,f49])).

fof(f117,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f43,f29])).

fof(f43,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f120,plain,(
    ! [X10,X8,X9] : k5_xboole_0(X8,k5_xboole_0(k3_xboole_0(X8,X9),X10)) = k5_xboole_0(k4_xboole_0(X8,X9),X10) ),
    inference(superposition,[],[f43,f37])).

fof(f557,plain,
    ( k4_xboole_0(sK0,sK2) != k5_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
    | ~ r1_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f28,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X1,X0) = k2_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f36,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f28,plain,(
    k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
    inference(cnf_transformation,[],[f24])).

fof(f1533,plain,(
    ! [X61,X62,X63] :
      ( r1_xboole_0(k3_xboole_0(X62,X63),X61)
      | ~ r1_xboole_0(k3_xboole_0(X61,X62),X63) ) ),
    inference(trivial_inequality_removal,[],[f1518])).

fof(f1518,plain,(
    ! [X61,X62,X63] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(k3_xboole_0(X62,X63),X61)
      | ~ r1_xboole_0(k3_xboole_0(X61,X62),X63) ) ),
    inference(superposition,[],[f92,f160])).

fof(f160,plain,(
    ! [X4,X5,X3] :
      ( k1_xboole_0 = k3_xboole_0(X3,k3_xboole_0(X4,X5))
      | ~ r1_xboole_0(k3_xboole_0(X3,X4),X5) ) ),
    inference(superposition,[],[f45,f41])).

fof(f92,plain,(
    ! [X4,X5] :
      ( k1_xboole_0 != k3_xboole_0(X5,X4)
      | r1_xboole_0(X4,X5) ) ),
    inference(superposition,[],[f42,f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:33:47 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.46  % (11134)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.46  % (11131)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.46  % (11126)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.46  % (11123)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.46  % (11124)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.46  % (11122)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.46  % (11125)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.48  % (11132)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.48  % (11133)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.48  % (11130)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.49  % (11119)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.49  % (11120)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.49  % (11127)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.49  % (11135)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.50  % (11121)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.50  % (11129)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.50  % (11128)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.52  % (11136)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 5.13/1.01  % (11123)Time limit reached!
% 5.13/1.01  % (11123)------------------------------
% 5.13/1.01  % (11123)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.13/1.02  % (11123)Termination reason: Time limit
% 5.13/1.02  % (11123)Termination phase: Saturation
% 5.13/1.02  
% 5.13/1.02  % (11123)Memory used [KB]: 14328
% 5.13/1.02  % (11123)Time elapsed: 0.602 s
% 5.13/1.02  % (11123)------------------------------
% 5.13/1.02  % (11123)------------------------------
% 5.66/1.18  % (11122)Refutation found. Thanks to Tanya!
% 5.66/1.18  % SZS status Theorem for theBenchmark
% 5.66/1.18  % SZS output start Proof for theBenchmark
% 5.66/1.18  fof(f13684,plain,(
% 5.66/1.18    $false),
% 5.66/1.18    inference(subsumption_resolution,[],[f13682,f27])).
% 5.66/1.18  fof(f27,plain,(
% 5.66/1.18    r1_tarski(sK2,sK1)),
% 5.66/1.18    inference(cnf_transformation,[],[f24])).
% 5.66/1.18  fof(f24,plain,(
% 5.66/1.18    k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) & r1_tarski(sK2,sK1)),
% 5.66/1.18    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f23])).
% 5.66/1.18  fof(f23,plain,(
% 5.66/1.18    ? [X0,X1,X2] : (k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) & r1_tarski(X2,X1)) => (k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) & r1_tarski(sK2,sK1))),
% 5.66/1.18    introduced(choice_axiom,[])).
% 5.66/1.18  fof(f20,plain,(
% 5.66/1.18    ? [X0,X1,X2] : (k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) & r1_tarski(X2,X1))),
% 5.66/1.18    inference(ennf_transformation,[],[f19])).
% 5.66/1.18  fof(f19,negated_conjecture,(
% 5.66/1.18    ~! [X0,X1,X2] : (r1_tarski(X2,X1) => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))))),
% 5.66/1.18    inference(negated_conjecture,[],[f18])).
% 5.66/1.18  fof(f18,conjecture,(
% 5.66/1.18    ! [X0,X1,X2] : (r1_tarski(X2,X1) => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))))),
% 5.66/1.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_xboole_1)).
% 5.66/1.18  fof(f13682,plain,(
% 5.66/1.18    ~r1_tarski(sK2,sK1)),
% 5.66/1.18    inference(trivial_inequality_removal,[],[f13674])).
% 5.66/1.18  fof(f13674,plain,(
% 5.66/1.18    k4_xboole_0(sK0,sK2) != k4_xboole_0(sK0,sK2) | ~r1_tarski(sK2,sK1)),
% 5.66/1.18    inference(superposition,[],[f13670,f61])).
% 5.66/1.18  fof(f61,plain,(
% 5.66/1.18    ( ! [X2,X3] : (k3_xboole_0(X3,X2) = X2 | ~r1_tarski(X2,X3)) )),
% 5.66/1.18    inference(superposition,[],[f38,f35])).
% 5.66/1.18  fof(f35,plain,(
% 5.66/1.18    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 5.66/1.18    inference(cnf_transformation,[],[f1])).
% 5.66/1.18  fof(f1,axiom,(
% 5.66/1.18    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 5.66/1.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 5.66/1.18  fof(f38,plain,(
% 5.66/1.18    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 5.66/1.18    inference(cnf_transformation,[],[f21])).
% 5.66/1.18  fof(f21,plain,(
% 5.66/1.18    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 5.66/1.18    inference(ennf_transformation,[],[f9])).
% 5.66/1.18  fof(f9,axiom,(
% 5.66/1.18    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 5.66/1.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 5.66/1.18  fof(f13670,plain,(
% 5.66/1.18    k4_xboole_0(sK0,sK2) != k4_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 5.66/1.18    inference(subsumption_resolution,[],[f13669,f7591])).
% 5.66/1.18  fof(f7591,plain,(
% 5.66/1.18    ( ! [X152,X151,X149,X150] : (r1_xboole_0(k3_xboole_0(X152,k4_xboole_0(X149,X150)),k4_xboole_0(X150,X151))) )),
% 5.66/1.18    inference(subsumption_resolution,[],[f7515,f210])).
% 5.66/1.18  fof(f210,plain,(
% 5.66/1.18    ( ! [X3] : (k1_xboole_0 = k3_xboole_0(X3,k1_xboole_0)) )),
% 5.66/1.18    inference(superposition,[],[f203,f35])).
% 5.66/1.18  fof(f203,plain,(
% 5.66/1.18    ( ! [X6] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X6)) )),
% 5.66/1.18    inference(forward_demodulation,[],[f191,f29])).
% 5.66/1.18  fof(f29,plain,(
% 5.66/1.18    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 5.66/1.18    inference(cnf_transformation,[],[f16])).
% 5.66/1.18  fof(f16,axiom,(
% 5.66/1.18    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 5.66/1.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 5.66/1.18  fof(f191,plain,(
% 5.66/1.18    ( ! [X6,X5] : (k1_xboole_0 = k3_xboole_0(k5_xboole_0(X5,X5),X6)) )),
% 5.66/1.18    inference(superposition,[],[f46,f29])).
% 5.66/1.18  fof(f46,plain,(
% 5.66/1.18    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) )),
% 5.66/1.18    inference(cnf_transformation,[],[f6])).
% 5.66/1.18  fof(f6,axiom,(
% 5.66/1.18    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 5.66/1.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).
% 5.66/1.18  fof(f7515,plain,(
% 5.66/1.18    ( ! [X152,X151,X149,X150] : (k1_xboole_0 != k3_xboole_0(X152,k1_xboole_0) | r1_xboole_0(k3_xboole_0(X152,k4_xboole_0(X149,X150)),k4_xboole_0(X150,X151))) )),
% 5.66/1.18    inference(superposition,[],[f170,f1261])).
% 5.66/1.18  fof(f1261,plain,(
% 5.66/1.18    ( ! [X19,X20,X18] : (k1_xboole_0 = k3_xboole_0(k4_xboole_0(X18,X19),k4_xboole_0(X19,X20))) )),
% 5.66/1.18    inference(forward_demodulation,[],[f1235,f206])).
% 5.66/1.18  fof(f206,plain,(
% 5.66/1.18    ( ! [X6] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X6)) )),
% 5.66/1.18    inference(backward_demodulation,[],[f113,f203])).
% 5.66/1.18  fof(f113,plain,(
% 5.66/1.18    ( ! [X6] : (k3_xboole_0(k1_xboole_0,X6) = k4_xboole_0(k1_xboole_0,X6)) )),
% 5.66/1.18    inference(superposition,[],[f37,f49])).
% 5.66/1.18  fof(f49,plain,(
% 5.66/1.18    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 5.66/1.18    inference(superposition,[],[f34,f30])).
% 5.66/1.18  fof(f30,plain,(
% 5.66/1.18    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 5.66/1.18    inference(cnf_transformation,[],[f12])).
% 5.66/1.18  fof(f12,axiom,(
% 5.66/1.18    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 5.66/1.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 5.66/1.18  fof(f34,plain,(
% 5.66/1.18    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 5.66/1.18    inference(cnf_transformation,[],[f2])).
% 5.66/1.18  fof(f2,axiom,(
% 5.66/1.18    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 5.66/1.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 5.66/1.18  fof(f37,plain,(
% 5.66/1.18    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 5.66/1.18    inference(cnf_transformation,[],[f4])).
% 5.66/1.18  fof(f4,axiom,(
% 5.66/1.18    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 5.66/1.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 5.66/1.18  fof(f1235,plain,(
% 5.66/1.18    ( ! [X19,X20,X18] : (k3_xboole_0(k4_xboole_0(X18,X19),k4_xboole_0(X19,X20)) = k4_xboole_0(k1_xboole_0,X20)) )),
% 5.66/1.18    inference(superposition,[],[f44,f1170])).
% 5.66/1.18  fof(f1170,plain,(
% 5.66/1.18    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 5.66/1.18    inference(backward_demodulation,[],[f208,f1167])).
% 5.66/1.18  fof(f1167,plain,(
% 5.66/1.18    ( ! [X6,X7] : (k1_xboole_0 = k3_xboole_0(X6,k4_xboole_0(X7,X7))) )),
% 5.66/1.18    inference(subsumption_resolution,[],[f1120,f31])).
% 5.66/1.18  fof(f31,plain,(
% 5.66/1.18    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 5.66/1.18    inference(cnf_transformation,[],[f13])).
% 5.66/1.18  fof(f13,axiom,(
% 5.66/1.18    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 5.66/1.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 5.66/1.18  fof(f1120,plain,(
% 5.66/1.18    ( ! [X6,X7] : (k1_xboole_0 = k3_xboole_0(X6,k4_xboole_0(X7,X7)) | ~r1_xboole_0(k4_xboole_0(X6,X7),X7)) )),
% 5.66/1.18    inference(superposition,[],[f208,f41])).
% 5.66/1.18  fof(f41,plain,(
% 5.66/1.18    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 5.66/1.18    inference(cnf_transformation,[],[f26])).
% 5.66/1.18  fof(f26,plain,(
% 5.66/1.18    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 5.66/1.18    inference(nnf_transformation,[],[f3])).
% 5.66/1.18  fof(f3,axiom,(
% 5.66/1.18    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 5.66/1.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 5.66/1.18  fof(f208,plain,(
% 5.66/1.18    ( ! [X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X1)) = k3_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 5.66/1.18    inference(forward_demodulation,[],[f207,f37])).
% 5.66/1.18  fof(f207,plain,(
% 5.66/1.18    ( ! [X0,X1] : (k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = k3_xboole_0(X0,k4_xboole_0(X1,X1))) )),
% 5.66/1.18    inference(forward_demodulation,[],[f194,f44])).
% 5.66/1.18  fof(f194,plain,(
% 5.66/1.18    ( ! [X0,X1] : (k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = k4_xboole_0(k3_xboole_0(X0,X1),X1)) )),
% 5.66/1.18    inference(superposition,[],[f37,f46])).
% 5.66/1.18  fof(f44,plain,(
% 5.66/1.18    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 5.66/1.18    inference(cnf_transformation,[],[f11])).
% 5.66/1.18  fof(f11,axiom,(
% 5.66/1.18    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 5.66/1.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 5.66/1.18  fof(f170,plain,(
% 5.66/1.18    ( ! [X19,X20,X18] : (k1_xboole_0 != k3_xboole_0(X18,k3_xboole_0(X19,X20)) | r1_xboole_0(k3_xboole_0(X18,X19),X20)) )),
% 5.66/1.18    inference(superposition,[],[f42,f45])).
% 5.66/1.18  fof(f45,plain,(
% 5.66/1.18    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 5.66/1.18    inference(cnf_transformation,[],[f7])).
% 5.66/1.18  fof(f7,axiom,(
% 5.66/1.18    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 5.66/1.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 5.66/1.18  fof(f42,plain,(
% 5.66/1.18    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 5.66/1.18    inference(cnf_transformation,[],[f26])).
% 5.66/1.18  fof(f13669,plain,(
% 5.66/1.18    ~r1_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK2)) | k4_xboole_0(sK0,sK2) != k4_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 5.66/1.18    inference(forward_demodulation,[],[f13624,f35])).
% 5.66/1.18  fof(f13624,plain,(
% 5.66/1.18    ~r1_xboole_0(k3_xboole_0(k4_xboole_0(sK0,sK1),sK0),k4_xboole_0(sK1,sK2)) | k4_xboole_0(sK0,sK2) != k4_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 5.66/1.18    inference(resolution,[],[f1533,f5477])).
% 5.66/1.18  fof(f5477,plain,(
% 5.66/1.18    ~r1_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK0,sK1)) | k4_xboole_0(sK0,sK2) != k4_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 5.66/1.18    inference(backward_demodulation,[],[f557,f5476])).
% 5.66/1.18  fof(f5476,plain,(
% 5.66/1.18    ( ! [X43,X44,X42] : (k4_xboole_0(X42,k3_xboole_0(X43,X44)) = k5_xboole_0(k4_xboole_0(X42,X43),k3_xboole_0(X42,k4_xboole_0(X43,X44)))) )),
% 5.66/1.18    inference(forward_demodulation,[],[f5475,f44])).
% 5.66/1.18  fof(f5475,plain,(
% 5.66/1.18    ( ! [X43,X44,X42] : (k5_xboole_0(k4_xboole_0(X42,X43),k4_xboole_0(k3_xboole_0(X42,X43),X44)) = k4_xboole_0(X42,k3_xboole_0(X43,X44))) )),
% 5.66/1.18    inference(forward_demodulation,[],[f5474,f37])).
% 5.66/1.18  fof(f5474,plain,(
% 5.66/1.18    ( ! [X43,X44,X42] : (k5_xboole_0(k4_xboole_0(X42,X43),k4_xboole_0(k3_xboole_0(X42,X43),X44)) = k5_xboole_0(X42,k3_xboole_0(X42,k3_xboole_0(X43,X44)))) )),
% 5.66/1.18    inference(forward_demodulation,[],[f5430,f45])).
% 5.66/1.18  fof(f5430,plain,(
% 5.66/1.18    ( ! [X43,X44,X42] : (k5_xboole_0(k4_xboole_0(X42,X43),k4_xboole_0(k3_xboole_0(X42,X43),X44)) = k5_xboole_0(X42,k3_xboole_0(k3_xboole_0(X42,X43),X44))) )),
% 5.66/1.18    inference(superposition,[],[f120,f285])).
% 5.66/1.18  fof(f285,plain,(
% 5.66/1.18    ( ! [X6,X5] : (k3_xboole_0(X5,X6) = k5_xboole_0(X5,k4_xboole_0(X5,X6))) )),
% 5.66/1.18    inference(superposition,[],[f137,f37])).
% 5.66/1.18  fof(f137,plain,(
% 5.66/1.18    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 5.66/1.18    inference(forward_demodulation,[],[f117,f49])).
% 5.66/1.18  fof(f117,plain,(
% 5.66/1.18    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 5.66/1.18    inference(superposition,[],[f43,f29])).
% 5.66/1.18  fof(f43,plain,(
% 5.66/1.18    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 5.66/1.18    inference(cnf_transformation,[],[f15])).
% 5.66/1.18  fof(f15,axiom,(
% 5.66/1.18    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 5.66/1.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 5.66/1.18  fof(f120,plain,(
% 5.66/1.18    ( ! [X10,X8,X9] : (k5_xboole_0(X8,k5_xboole_0(k3_xboole_0(X8,X9),X10)) = k5_xboole_0(k4_xboole_0(X8,X9),X10)) )),
% 5.66/1.18    inference(superposition,[],[f43,f37])).
% 5.66/1.18  fof(f557,plain,(
% 5.66/1.18    k4_xboole_0(sK0,sK2) != k5_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) | ~r1_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK0,sK1))),
% 5.66/1.18    inference(superposition,[],[f28,f105])).
% 5.66/1.18  fof(f105,plain,(
% 5.66/1.18    ( ! [X0,X1] : (k5_xboole_0(X1,X0) = k2_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 5.66/1.18    inference(superposition,[],[f36,f39])).
% 5.66/1.18  fof(f39,plain,(
% 5.66/1.18    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 5.66/1.18    inference(cnf_transformation,[],[f25])).
% 5.66/1.18  fof(f25,plain,(
% 5.66/1.18    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 5.66/1.18    inference(nnf_transformation,[],[f14])).
% 5.66/1.18  fof(f14,axiom,(
% 5.66/1.18    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 5.66/1.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 5.66/1.18  fof(f36,plain,(
% 5.66/1.18    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 5.66/1.18    inference(cnf_transformation,[],[f17])).
% 5.66/1.18  fof(f17,axiom,(
% 5.66/1.18    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 5.66/1.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 5.66/1.18  fof(f28,plain,(
% 5.66/1.18    k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 5.66/1.18    inference(cnf_transformation,[],[f24])).
% 5.66/1.18  fof(f1533,plain,(
% 5.66/1.18    ( ! [X61,X62,X63] : (r1_xboole_0(k3_xboole_0(X62,X63),X61) | ~r1_xboole_0(k3_xboole_0(X61,X62),X63)) )),
% 5.66/1.18    inference(trivial_inequality_removal,[],[f1518])).
% 5.66/1.18  fof(f1518,plain,(
% 5.66/1.18    ( ! [X61,X62,X63] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k3_xboole_0(X62,X63),X61) | ~r1_xboole_0(k3_xboole_0(X61,X62),X63)) )),
% 5.66/1.18    inference(superposition,[],[f92,f160])).
% 5.66/1.18  fof(f160,plain,(
% 5.66/1.18    ( ! [X4,X5,X3] : (k1_xboole_0 = k3_xboole_0(X3,k3_xboole_0(X4,X5)) | ~r1_xboole_0(k3_xboole_0(X3,X4),X5)) )),
% 5.66/1.18    inference(superposition,[],[f45,f41])).
% 5.66/1.18  fof(f92,plain,(
% 5.66/1.18    ( ! [X4,X5] : (k1_xboole_0 != k3_xboole_0(X5,X4) | r1_xboole_0(X4,X5)) )),
% 5.66/1.18    inference(superposition,[],[f42,f35])).
% 5.66/1.18  % SZS output end Proof for theBenchmark
% 5.66/1.18  % (11122)------------------------------
% 5.66/1.18  % (11122)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.66/1.18  % (11122)Termination reason: Refutation
% 5.66/1.18  
% 5.66/1.18  % (11122)Memory used [KB]: 9338
% 5.66/1.18  % (11122)Time elapsed: 0.760 s
% 5.66/1.18  % (11122)------------------------------
% 5.66/1.18  % (11122)------------------------------
% 6.49/1.18  % (11118)Success in time 0.824 s
%------------------------------------------------------------------------------
