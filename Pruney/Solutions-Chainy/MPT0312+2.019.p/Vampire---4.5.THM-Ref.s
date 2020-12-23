%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:09 EST 2020

% Result     : Theorem 5.01s
% Output     : Refutation 5.01s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 821 expanded)
%              Number of leaves         :   17 ( 262 expanded)
%              Depth                    :   19
%              Number of atoms          :  127 ( 983 expanded)
%              Number of equality atoms :   70 ( 796 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3341,plain,(
    $false ),
    inference(global_subsumption,[],[f3320,f3333,f3340])).

fof(f3340,plain,
    ( ~ sP6(sK5(sK3,sK2,sK2),sK2,sK3)
    | ~ r2_hidden(sK5(sK3,sK2,sK2),sK2) ),
    inference(equality_resolution,[],[f379])).

fof(f379,plain,(
    ! [X1] :
      ( k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(sK0,X1)
      | ~ sP6(sK5(sK3,sK2,X1),sK2,sK3)
      | ~ r2_hidden(sK5(sK3,sK2,X1),X1) ) ),
    inference(superposition,[],[f359,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) = X2
      | ~ sP6(sK5(X0,X1,X2),X1,X0)
      | ~ r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(forward_demodulation,[],[f63,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ sP6(sK5(X0,X1,X2),X1,X0)
      | ~ r2_hidden(sK5(X0,X1,X2),X2)
      | k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = X2 ) ),
    inference(definition_unfolding,[],[f49,f55])).

fof(f55,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f36,f54])).

fof(f54,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f33,f53])).

fof(f53,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f34,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f41,f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f41,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f34,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ sP6(sK5(X0,X1,X2),X1,X0)
      | ~ r2_hidden(sK5(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f359,plain,(
    k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(sK0,k5_xboole_0(sK3,k5_xboole_0(sK2,k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK2))))) ),
    inference(forward_demodulation,[],[f358,f75])).

fof(f75,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f74,f28])).

fof(f28,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f74,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0 ),
    inference(forward_demodulation,[],[f73,f72])).

fof(f72,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f71,f28])).

fof(f71,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),X0) = X0 ),
    inference(forward_demodulation,[],[f61,f60])).

fof(f60,plain,(
    ! [X0] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f31,f54])).

fof(f31,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f61,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k3_enumset1(X0,X0,X0,X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f32,f55])).

fof(f32,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f73,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(backward_demodulation,[],[f70,f42])).

fof(f70,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),X0)) = X0 ),
    inference(backward_demodulation,[],[f58,f59])).

fof(f59,plain,(
    ! [X0] : k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f30,f54])).

fof(f30,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f58,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)))) = X0 ),
    inference(definition_unfolding,[],[f29,f56])).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f35,f55])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f29,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f358,plain,(
    k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(k5_xboole_0(sK0,k1_xboole_0),k5_xboole_0(sK3,k5_xboole_0(sK2,k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK2))))) ),
    inference(forward_demodulation,[],[f357,f28])).

fof(f357,plain,(
    k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)),k5_xboole_0(sK3,k5_xboole_0(sK2,k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK2))))) ),
    inference(forward_demodulation,[],[f339,f142])).

fof(f142,plain,(
    sK1 = k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f25,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f37,f54])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f25,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X2) != k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X2) != k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => k2_zfmisc_1(X0,X2) = k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => k2_zfmisc_1(X0,X2) = k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_zfmisc_1)).

fof(f339,plain,(
    k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1)))),k5_xboole_0(sK3,k5_xboole_0(sK2,k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK2))))) ),
    inference(superposition,[],[f57,f81])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)),k3_tarski(k3_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))) = k2_zfmisc_1(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))),k5_xboole_0(X2,k5_xboole_0(X3,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3))))) ),
    inference(forward_demodulation,[],[f80,f42])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)),k3_tarski(k3_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))) = k2_zfmisc_1(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))),k5_xboole_0(X2,k5_xboole_0(X3,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3))))) ),
    inference(forward_demodulation,[],[f67,f42])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))),k5_xboole_0(k5_xboole_0(X2,X3),k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)))) = k5_xboole_0(k5_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)),k3_tarski(k3_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))) ),
    inference(definition_unfolding,[],[f51,f55,f55,f55])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f57,plain,(
    k2_zfmisc_1(sK0,sK2) != k5_xboole_0(k5_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)),k3_tarski(k3_enumset1(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)))) ),
    inference(definition_unfolding,[],[f27,f55])).

fof(f27,plain,(
    k2_zfmisc_1(sK0,sK2) != k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f22])).

fof(f3333,plain,(
    sP6(sK5(sK3,sK2,sK2),sK2,sK3) ),
    inference(unit_resulting_resolution,[],[f3320,f3323,f43])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( sP6(X3,X1,X0)
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f3323,plain,(
    r2_hidden(sK5(sK3,sK2,sK2),sK3) ),
    inference(unit_resulting_resolution,[],[f26,f3320,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f26,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f3320,plain,(
    r2_hidden(sK5(sK3,sK2,sK2),sK2) ),
    inference(duplicate_literal_removal,[],[f3318])).

fof(f3318,plain,
    ( r2_hidden(sK5(sK3,sK2,sK2),sK2)
    | r2_hidden(sK5(sK3,sK2,sK2),sK2) ),
    inference(resolution,[],[f3312,f45])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( ~ sP6(X3,X1,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f3312,plain,
    ( sP6(sK5(sK3,sK2,sK2),sK2,sK3)
    | r2_hidden(sK5(sK3,sK2,sK2),sK2) ),
    inference(equality_resolution,[],[f378])).

fof(f378,plain,(
    ! [X0] :
      ( k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(sK0,X0)
      | sP6(sK5(sK3,sK2,X0),sK2,sK3)
      | r2_hidden(sK5(sK3,sK2,X0),X0) ) ),
    inference(superposition,[],[f359,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) = X2
      | sP6(sK5(X0,X1,X2),X1,X0)
      | r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(forward_demodulation,[],[f64,f42])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( sP6(sK5(X0,X1,X2),X1,X0)
      | r2_hidden(sK5(X0,X1,X2),X2)
      | k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = X2 ) ),
    inference(definition_unfolding,[],[f48,f55])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( sP6(sK5(X0,X1,X2),X1,X0)
      | r2_hidden(sK5(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:54:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (22465)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.50  % (22465)Refutation not found, incomplete strategy% (22465)------------------------------
% 0.21/0.50  % (22465)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (22459)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (22473)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.51  % (22465)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (22465)Memory used [KB]: 10618
% 0.21/0.51  % (22465)Time elapsed: 0.095 s
% 0.21/0.51  % (22465)------------------------------
% 0.21/0.51  % (22465)------------------------------
% 0.21/0.51  % (22473)Refutation not found, incomplete strategy% (22473)------------------------------
% 0.21/0.51  % (22473)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (22460)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (22473)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (22473)Memory used [KB]: 10618
% 0.21/0.51  % (22473)Time elapsed: 0.096 s
% 0.21/0.51  % (22473)------------------------------
% 0.21/0.51  % (22473)------------------------------
% 0.21/0.51  % (22456)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (22456)Refutation not found, incomplete strategy% (22456)------------------------------
% 0.21/0.51  % (22456)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (22456)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (22456)Memory used [KB]: 1663
% 0.21/0.51  % (22456)Time elapsed: 0.079 s
% 0.21/0.51  % (22456)------------------------------
% 0.21/0.51  % (22456)------------------------------
% 0.21/0.52  % (22467)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (22475)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (22476)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (22470)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (22483)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (22468)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (22478)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (22458)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (22461)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (22480)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (22462)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (22457)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (22472)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (22484)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (22481)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (22485)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (22482)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (22463)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.55  % (22471)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (22474)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (22477)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (22464)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.56  % (22466)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.56  % (22469)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.56  % (22479)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.56  % (22466)Refutation not found, incomplete strategy% (22466)------------------------------
% 0.21/0.56  % (22466)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (22466)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (22466)Memory used [KB]: 10618
% 0.21/0.56  % (22466)Time elapsed: 0.150 s
% 0.21/0.56  % (22466)------------------------------
% 0.21/0.56  % (22466)------------------------------
% 2.10/0.63  % (22487)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.10/0.64  % (22486)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.10/0.70  % (22488)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.10/0.70  % (22489)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.85/0.76  % (22487)Refutation not found, incomplete strategy% (22487)------------------------------
% 2.85/0.76  % (22487)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.85/0.76  % (22487)Termination reason: Refutation not found, incomplete strategy
% 2.85/0.76  
% 2.85/0.76  % (22487)Memory used [KB]: 6140
% 2.85/0.76  % (22487)Time elapsed: 0.125 s
% 2.85/0.76  % (22487)------------------------------
% 2.85/0.76  % (22487)------------------------------
% 3.40/0.84  % (22461)Time limit reached!
% 3.40/0.84  % (22461)------------------------------
% 3.40/0.84  % (22461)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.40/0.84  % (22461)Termination reason: Time limit
% 3.40/0.84  
% 3.40/0.84  % (22461)Memory used [KB]: 10618
% 3.40/0.84  % (22461)Time elapsed: 0.435 s
% 3.40/0.84  % (22461)------------------------------
% 3.40/0.84  % (22461)------------------------------
% 3.98/0.89  % (22490)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 4.17/0.92  % (22468)Time limit reached!
% 4.17/0.92  % (22468)------------------------------
% 4.17/0.92  % (22468)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.17/0.92  % (22468)Termination reason: Time limit
% 4.17/0.92  % (22468)Termination phase: Saturation
% 4.17/0.92  
% 4.17/0.92  % (22468)Memory used [KB]: 11001
% 4.17/0.92  % (22468)Time elapsed: 0.500 s
% 4.17/0.92  % (22468)------------------------------
% 4.17/0.92  % (22468)------------------------------
% 4.32/0.93  % (22457)Time limit reached!
% 4.32/0.93  % (22457)------------------------------
% 4.32/0.93  % (22457)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.32/0.93  % (22457)Termination reason: Time limit
% 4.32/0.93  
% 4.32/0.93  % (22457)Memory used [KB]: 8827
% 4.32/0.93  % (22457)Time elapsed: 0.514 s
% 4.32/0.93  % (22457)------------------------------
% 4.32/0.93  % (22457)------------------------------
% 4.32/0.99  % (22491)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 4.32/1.00  % (22489)Time limit reached!
% 4.32/1.00  % (22489)------------------------------
% 4.32/1.00  % (22489)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.32/1.00  % (22489)Termination reason: Time limit
% 4.32/1.00  
% 4.32/1.00  % (22489)Memory used [KB]: 8571
% 4.32/1.00  % (22489)Time elapsed: 0.417 s
% 4.32/1.00  % (22489)------------------------------
% 4.32/1.00  % (22489)------------------------------
% 4.32/1.01  % (22463)Time limit reached!
% 4.32/1.01  % (22463)------------------------------
% 4.32/1.01  % (22463)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.32/1.02  % (22472)Time limit reached!
% 4.32/1.02  % (22472)------------------------------
% 4.32/1.02  % (22472)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.32/1.02  % (22472)Termination reason: Time limit
% 4.32/1.02  
% 4.32/1.02  % (22472)Memory used [KB]: 14583
% 4.32/1.02  % (22472)Time elapsed: 0.606 s
% 4.32/1.02  % (22472)------------------------------
% 4.32/1.02  % (22472)------------------------------
% 4.32/1.02  % (22463)Termination reason: Time limit
% 4.32/1.02  % (22463)Termination phase: Saturation
% 4.32/1.02  
% 4.32/1.02  % (22463)Memory used [KB]: 12792
% 4.32/1.02  % (22463)Time elapsed: 0.600 s
% 4.32/1.02  % (22463)------------------------------
% 4.32/1.02  % (22463)------------------------------
% 5.01/1.04  % (22484)Time limit reached!
% 5.01/1.04  % (22484)------------------------------
% 5.01/1.04  % (22484)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.01/1.04  % (22484)Termination reason: Time limit
% 5.01/1.04  % (22484)Termination phase: Saturation
% 5.01/1.04  
% 5.01/1.04  % (22484)Memory used [KB]: 8187
% 5.01/1.04  % (22484)Time elapsed: 0.600 s
% 5.01/1.04  % (22484)------------------------------
% 5.01/1.04  % (22484)------------------------------
% 5.01/1.05  % (22492)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 5.01/1.06  % (22493)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 5.01/1.06  % (22480)Refutation found. Thanks to Tanya!
% 5.01/1.06  % SZS status Theorem for theBenchmark
% 5.01/1.06  % SZS output start Proof for theBenchmark
% 5.01/1.06  fof(f3341,plain,(
% 5.01/1.06    $false),
% 5.01/1.06    inference(global_subsumption,[],[f3320,f3333,f3340])).
% 5.01/1.06  fof(f3340,plain,(
% 5.01/1.06    ~sP6(sK5(sK3,sK2,sK2),sK2,sK3) | ~r2_hidden(sK5(sK3,sK2,sK2),sK2)),
% 5.01/1.06    inference(equality_resolution,[],[f379])).
% 5.01/1.06  fof(f379,plain,(
% 5.01/1.06    ( ! [X1] : (k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(sK0,X1) | ~sP6(sK5(sK3,sK2,X1),sK2,sK3) | ~r2_hidden(sK5(sK3,sK2,X1),X1)) )),
% 5.01/1.06    inference(superposition,[],[f359,f76])).
% 5.01/1.06  fof(f76,plain,(
% 5.01/1.06    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) = X2 | ~sP6(sK5(X0,X1,X2),X1,X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) )),
% 5.01/1.06    inference(forward_demodulation,[],[f63,f42])).
% 5.01/1.08  fof(f42,plain,(
% 5.01/1.08    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 5.01/1.08    inference(cnf_transformation,[],[f9])).
% 5.01/1.08  fof(f9,axiom,(
% 5.01/1.08    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 5.01/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 5.01/1.08  fof(f63,plain,(
% 5.01/1.08    ( ! [X2,X0,X1] : (~sP6(sK5(X0,X1,X2),X1,X0) | ~r2_hidden(sK5(X0,X1,X2),X2) | k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = X2) )),
% 5.01/1.08    inference(definition_unfolding,[],[f49,f55])).
% 5.01/1.08  fof(f55,plain,(
% 5.01/1.08    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 5.01/1.08    inference(definition_unfolding,[],[f36,f54])).
% 5.01/1.08  fof(f54,plain,(
% 5.01/1.08    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 5.01/1.08    inference(definition_unfolding,[],[f33,f53])).
% 5.01/1.08  fof(f53,plain,(
% 5.01/1.08    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 5.01/1.08    inference(definition_unfolding,[],[f34,f52])).
% 5.01/1.08  fof(f52,plain,(
% 5.01/1.08    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 5.01/1.08    inference(definition_unfolding,[],[f41,f50])).
% 5.01/1.08  fof(f50,plain,(
% 5.01/1.08    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 5.01/1.08    inference(cnf_transformation,[],[f14])).
% 5.01/1.08  fof(f14,axiom,(
% 5.01/1.08    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 5.01/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 5.01/1.08  fof(f41,plain,(
% 5.01/1.08    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 5.01/1.08    inference(cnf_transformation,[],[f13])).
% 5.01/1.08  fof(f13,axiom,(
% 5.01/1.08    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 5.01/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 5.01/1.08  fof(f34,plain,(
% 5.01/1.08    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 5.01/1.08    inference(cnf_transformation,[],[f12])).
% 5.01/1.08  fof(f12,axiom,(
% 5.01/1.08    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 5.01/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 5.01/1.08  fof(f33,plain,(
% 5.01/1.08    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 5.01/1.08    inference(cnf_transformation,[],[f15])).
% 5.01/1.08  fof(f15,axiom,(
% 5.01/1.08    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 5.01/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 5.01/1.08  fof(f36,plain,(
% 5.01/1.08    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 5.01/1.08    inference(cnf_transformation,[],[f11])).
% 5.01/1.08  fof(f11,axiom,(
% 5.01/1.08    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 5.01/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 5.01/1.08  fof(f49,plain,(
% 5.01/1.08    ( ! [X2,X0,X1] : (~sP6(sK5(X0,X1,X2),X1,X0) | ~r2_hidden(sK5(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 5.01/1.08    inference(cnf_transformation,[],[f2])).
% 5.01/1.08  fof(f2,axiom,(
% 5.01/1.08    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 5.01/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 5.01/1.08  fof(f359,plain,(
% 5.01/1.08    k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(sK0,k5_xboole_0(sK3,k5_xboole_0(sK2,k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK2)))))),
% 5.01/1.08    inference(forward_demodulation,[],[f358,f75])).
% 5.01/1.08  fof(f75,plain,(
% 5.01/1.08    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 5.01/1.08    inference(forward_demodulation,[],[f74,f28])).
% 5.01/1.08  fof(f28,plain,(
% 5.01/1.08    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 5.01/1.08    inference(cnf_transformation,[],[f10])).
% 5.01/1.08  fof(f10,axiom,(
% 5.01/1.08    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 5.01/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 5.01/1.08  fof(f74,plain,(
% 5.01/1.08    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0) )),
% 5.01/1.08    inference(forward_demodulation,[],[f73,f72])).
% 5.01/1.08  fof(f72,plain,(
% 5.01/1.08    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 5.01/1.08    inference(forward_demodulation,[],[f71,f28])).
% 5.01/1.08  fof(f71,plain,(
% 5.01/1.08    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),X0) = X0) )),
% 5.01/1.08    inference(forward_demodulation,[],[f61,f60])).
% 5.01/1.08  fof(f60,plain,(
% 5.01/1.08    ( ! [X0] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X0)) = X0) )),
% 5.01/1.08    inference(definition_unfolding,[],[f31,f54])).
% 5.01/1.08  fof(f31,plain,(
% 5.01/1.08    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 5.01/1.08    inference(cnf_transformation,[],[f19])).
% 5.01/1.08  fof(f19,plain,(
% 5.01/1.08    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 5.01/1.08    inference(rectify,[],[f3])).
% 5.01/1.08  fof(f3,axiom,(
% 5.01/1.08    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 5.01/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 5.01/1.08  fof(f61,plain,(
% 5.01/1.08    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k3_enumset1(X0,X0,X0,X0,X0))) = X0) )),
% 5.01/1.08    inference(definition_unfolding,[],[f32,f55])).
% 5.01/1.08  fof(f32,plain,(
% 5.01/1.08    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 5.01/1.08    inference(cnf_transformation,[],[f20])).
% 5.01/1.08  fof(f20,plain,(
% 5.01/1.08    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 5.01/1.08    inference(rectify,[],[f4])).
% 5.01/1.08  fof(f4,axiom,(
% 5.01/1.08    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 5.01/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 5.01/1.08  fof(f73,plain,(
% 5.01/1.08    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X0))) = X0) )),
% 5.01/1.08    inference(backward_demodulation,[],[f70,f42])).
% 5.01/1.08  fof(f70,plain,(
% 5.01/1.08    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),X0)) = X0) )),
% 5.01/1.08    inference(backward_demodulation,[],[f58,f59])).
% 5.01/1.08  fof(f59,plain,(
% 5.01/1.08    ( ! [X0] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0) )),
% 5.01/1.08    inference(definition_unfolding,[],[f30,f54])).
% 5.01/1.08  fof(f30,plain,(
% 5.01/1.08    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 5.01/1.08    inference(cnf_transformation,[],[f7])).
% 5.01/1.08  fof(f7,axiom,(
% 5.01/1.08    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 5.01/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 5.01/1.08  fof(f58,plain,(
% 5.01/1.08    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)))) = X0) )),
% 5.01/1.08    inference(definition_unfolding,[],[f29,f56])).
% 5.01/1.08  fof(f56,plain,(
% 5.01/1.08    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))))) )),
% 5.01/1.08    inference(definition_unfolding,[],[f35,f55])).
% 5.01/1.08  fof(f35,plain,(
% 5.01/1.08    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 5.01/1.08    inference(cnf_transformation,[],[f5])).
% 5.01/1.08  fof(f5,axiom,(
% 5.01/1.08    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 5.01/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 5.01/1.08  fof(f29,plain,(
% 5.01/1.08    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 5.01/1.08    inference(cnf_transformation,[],[f8])).
% 5.01/1.08  fof(f8,axiom,(
% 5.01/1.08    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 5.01/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 5.01/1.08  fof(f358,plain,(
% 5.01/1.08    k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(k5_xboole_0(sK0,k1_xboole_0),k5_xboole_0(sK3,k5_xboole_0(sK2,k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK2)))))),
% 5.01/1.08    inference(forward_demodulation,[],[f357,f28])).
% 5.01/1.08  fof(f357,plain,(
% 5.01/1.08    k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)),k5_xboole_0(sK3,k5_xboole_0(sK2,k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK2)))))),
% 5.01/1.08    inference(forward_demodulation,[],[f339,f142])).
% 5.01/1.08  fof(f142,plain,(
% 5.01/1.08    sK1 = k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1))),
% 5.01/1.08    inference(unit_resulting_resolution,[],[f25,f62])).
% 5.01/1.08  fof(f62,plain,(
% 5.01/1.08    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 5.01/1.08    inference(definition_unfolding,[],[f37,f54])).
% 5.01/1.08  fof(f37,plain,(
% 5.01/1.08    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 5.01/1.08    inference(cnf_transformation,[],[f23])).
% 5.01/1.08  fof(f23,plain,(
% 5.01/1.08    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 5.01/1.08    inference(ennf_transformation,[],[f6])).
% 5.01/1.08  fof(f6,axiom,(
% 5.01/1.08    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 5.01/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 5.01/1.08  fof(f25,plain,(
% 5.01/1.08    r1_tarski(sK0,sK1)),
% 5.01/1.08    inference(cnf_transformation,[],[f22])).
% 5.01/1.08  fof(f22,plain,(
% 5.01/1.08    ? [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X2) != k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) & r1_tarski(X2,X3) & r1_tarski(X0,X1))),
% 5.01/1.08    inference(flattening,[],[f21])).
% 5.01/1.08  fof(f21,plain,(
% 5.01/1.08    ? [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X2) != k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) & (r1_tarski(X2,X3) & r1_tarski(X0,X1)))),
% 5.01/1.08    inference(ennf_transformation,[],[f18])).
% 5.01/1.08  fof(f18,negated_conjecture,(
% 5.01/1.08    ~! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => k2_zfmisc_1(X0,X2) = k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)))),
% 5.01/1.08    inference(negated_conjecture,[],[f17])).
% 5.01/1.08  fof(f17,conjecture,(
% 5.01/1.08    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => k2_zfmisc_1(X0,X2) = k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)))),
% 5.01/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_zfmisc_1)).
% 5.01/1.08  fof(f339,plain,(
% 5.01/1.08    k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1)))),k5_xboole_0(sK3,k5_xboole_0(sK2,k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK2)))))),
% 5.01/1.08    inference(superposition,[],[f57,f81])).
% 5.01/1.08  fof(f81,plain,(
% 5.01/1.08    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)),k3_tarski(k3_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))) = k2_zfmisc_1(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))),k5_xboole_0(X2,k5_xboole_0(X3,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)))))) )),
% 5.01/1.08    inference(forward_demodulation,[],[f80,f42])).
% 5.01/1.08  fof(f80,plain,(
% 5.01/1.08    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)),k3_tarski(k3_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))) = k2_zfmisc_1(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))),k5_xboole_0(X2,k5_xboole_0(X3,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)))))) )),
% 5.01/1.08    inference(forward_demodulation,[],[f67,f42])).
% 5.01/1.08  fof(f67,plain,(
% 5.01/1.08    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))),k5_xboole_0(k5_xboole_0(X2,X3),k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)))) = k5_xboole_0(k5_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)),k3_tarski(k3_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))))) )),
% 5.01/1.08    inference(definition_unfolding,[],[f51,f55,f55,f55])).
% 5.01/1.08  fof(f51,plain,(
% 5.01/1.08    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 5.01/1.08    inference(cnf_transformation,[],[f16])).
% 5.01/1.08  fof(f16,axiom,(
% 5.01/1.08    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 5.01/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 5.01/1.08  fof(f57,plain,(
% 5.01/1.08    k2_zfmisc_1(sK0,sK2) != k5_xboole_0(k5_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)),k3_tarski(k3_enumset1(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2))))),
% 5.01/1.08    inference(definition_unfolding,[],[f27,f55])).
% 5.01/1.08  fof(f27,plain,(
% 5.01/1.08    k2_zfmisc_1(sK0,sK2) != k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2))),
% 5.01/1.08    inference(cnf_transformation,[],[f22])).
% 5.01/1.08  fof(f3333,plain,(
% 5.01/1.08    sP6(sK5(sK3,sK2,sK2),sK2,sK3)),
% 5.01/1.08    inference(unit_resulting_resolution,[],[f3320,f3323,f43])).
% 5.01/1.08  fof(f43,plain,(
% 5.01/1.08    ( ! [X0,X3,X1] : (sP6(X3,X1,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) )),
% 5.01/1.08    inference(cnf_transformation,[],[f2])).
% 5.01/1.09  fof(f3323,plain,(
% 5.01/1.09    r2_hidden(sK5(sK3,sK2,sK2),sK3)),
% 5.01/1.09    inference(unit_resulting_resolution,[],[f26,f3320,f38])).
% 5.01/1.09  fof(f38,plain,(
% 5.01/1.09    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 5.01/1.09    inference(cnf_transformation,[],[f24])).
% 5.01/1.09  fof(f24,plain,(
% 5.01/1.09    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 5.01/1.09    inference(ennf_transformation,[],[f1])).
% 5.01/1.09  fof(f1,axiom,(
% 5.01/1.09    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 5.01/1.09    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 5.01/1.09  fof(f26,plain,(
% 5.01/1.09    r1_tarski(sK2,sK3)),
% 5.01/1.09    inference(cnf_transformation,[],[f22])).
% 5.01/1.09  fof(f3320,plain,(
% 5.01/1.09    r2_hidden(sK5(sK3,sK2,sK2),sK2)),
% 5.01/1.09    inference(duplicate_literal_removal,[],[f3318])).
% 5.01/1.09  fof(f3318,plain,(
% 5.01/1.09    r2_hidden(sK5(sK3,sK2,sK2),sK2) | r2_hidden(sK5(sK3,sK2,sK2),sK2)),
% 5.01/1.09    inference(resolution,[],[f3312,f45])).
% 5.01/1.09  fof(f45,plain,(
% 5.01/1.09    ( ! [X0,X3,X1] : (~sP6(X3,X1,X0) | r2_hidden(X3,X1)) )),
% 5.01/1.09    inference(cnf_transformation,[],[f2])).
% 5.01/1.09  fof(f3312,plain,(
% 5.01/1.09    sP6(sK5(sK3,sK2,sK2),sK2,sK3) | r2_hidden(sK5(sK3,sK2,sK2),sK2)),
% 5.01/1.09    inference(equality_resolution,[],[f378])).
% 5.01/1.09  fof(f378,plain,(
% 5.01/1.09    ( ! [X0] : (k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(sK0,X0) | sP6(sK5(sK3,sK2,X0),sK2,sK3) | r2_hidden(sK5(sK3,sK2,X0),X0)) )),
% 5.01/1.09    inference(superposition,[],[f359,f77])).
% 5.01/1.09  fof(f77,plain,(
% 5.01/1.09    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) = X2 | sP6(sK5(X0,X1,X2),X1,X0) | r2_hidden(sK5(X0,X1,X2),X2)) )),
% 5.01/1.09    inference(forward_demodulation,[],[f64,f42])).
% 5.01/1.09  fof(f64,plain,(
% 5.01/1.09    ( ! [X2,X0,X1] : (sP6(sK5(X0,X1,X2),X1,X0) | r2_hidden(sK5(X0,X1,X2),X2) | k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = X2) )),
% 5.01/1.09    inference(definition_unfolding,[],[f48,f55])).
% 5.01/1.09  fof(f48,plain,(
% 5.01/1.09    ( ! [X2,X0,X1] : (sP6(sK5(X0,X1,X2),X1,X0) | r2_hidden(sK5(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 5.01/1.09    inference(cnf_transformation,[],[f2])).
% 5.01/1.09  % SZS output end Proof for theBenchmark
% 5.01/1.09  % (22480)------------------------------
% 5.01/1.09  % (22480)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.01/1.09  % (22480)Termination reason: Refutation
% 5.01/1.09  
% 5.01/1.09  % (22480)Memory used [KB]: 11129
% 5.01/1.09  % (22480)Time elapsed: 0.662 s
% 5.01/1.09  % (22480)------------------------------
% 5.01/1.09  % (22480)------------------------------
% 5.01/1.09  % (22455)Success in time 0.721 s
%------------------------------------------------------------------------------
