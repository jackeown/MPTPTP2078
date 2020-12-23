%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:07 EST 2020

% Result     : Theorem 1.63s
% Output     : Refutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :  143 (1298 expanded)
%              Number of leaves         :   23 ( 436 expanded)
%              Depth                    :   42
%              Number of atoms          :  289 (1638 expanded)
%              Number of equality atoms :  145 (1291 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f623,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f85,f88,f401,f619])).

fof(f619,plain,
    ( ~ spl2_1
    | spl2_2 ),
    inference(avatar_contradiction_clause,[],[f618])).

fof(f618,plain,
    ( $false
    | ~ spl2_1
    | spl2_2 ),
    inference(subsumption_resolution,[],[f617,f33])).

fof(f33,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f617,plain,
    ( k1_xboole_0 != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl2_1
    | spl2_2 ),
    inference(forward_demodulation,[],[f616,f591])).

fof(f591,plain,
    ( ! [X5] : k5_xboole_0(sK1,k5_xboole_0(X5,sK1)) = X5
    | ~ spl2_1 ),
    inference(superposition,[],[f568,f39])).

fof(f39,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f568,plain,
    ( ! [X0] : k5_xboole_0(sK1,k5_xboole_0(sK1,X0)) = X0
    | ~ spl2_1 ),
    inference(forward_demodulation,[],[f555,f35])).

fof(f35,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f555,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(X0,k1_xboole_0)))
    | ~ spl2_1 ),
    inference(superposition,[],[f548,f33])).

fof(f548,plain,
    ( ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(X3,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(X2,k5_xboole_0(X3,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))))
    | ~ spl2_1 ),
    inference(superposition,[],[f534,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f534,plain,
    ( ! [X1] : k5_xboole_0(X1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(X1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
    | ~ spl2_1 ),
    inference(superposition,[],[f530,f39])).

fof(f530,plain,
    ( ! [X0] : k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0)))
    | ~ spl2_1 ),
    inference(forward_demodulation,[],[f529,f50])).

fof(f529,plain,
    ( ! [X0] : k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0)
    | ~ spl2_1 ),
    inference(superposition,[],[f50,f525])).

fof(f525,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(sK1,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | ~ spl2_1 ),
    inference(backward_demodulation,[],[f440,f524])).

fof(f524,plain,
    ( k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
    | ~ spl2_1 ),
    inference(forward_demodulation,[],[f517,f35])).

fof(f517,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) = k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k1_xboole_0)
    | ~ spl2_1 ),
    inference(superposition,[],[f443,f33])).

fof(f443,plain,
    ( ! [X0] : k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0) = k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),X0))
    | ~ spl2_1 ),
    inference(superposition,[],[f50,f411])).

fof(f411,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
    | ~ spl2_1 ),
    inference(resolution,[],[f79,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k5_xboole_0(k5_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) ) ),
    inference(definition_unfolding,[],[f44,f63,f61,f63])).

fof(f61,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f43,f60])).

fof(f60,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f40,f59])).

fof(f59,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f41,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f49,f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f51,f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f52,f55])).

fof(f55,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f53,f54])).

fof(f54,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f53,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f49,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f63,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f36,f59])).

fof(f36,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).

fof(f79,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl2_1
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f440,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))))
    | ~ spl2_1 ),
    inference(superposition,[],[f411,f50])).

fof(f616,plain,
    ( k1_xboole_0 != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)))
    | ~ spl2_1
    | spl2_2 ),
    inference(backward_demodulation,[],[f84,f607])).

fof(f607,plain,
    ( ! [X0] : k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(X0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) = k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0))
    | ~ spl2_1 ),
    inference(superposition,[],[f543,f39])).

fof(f543,plain,
    ( ! [X0] : k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),X0)) = k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0))
    | ~ spl2_1 ),
    inference(forward_demodulation,[],[f542,f50])).

fof(f542,plain,
    ( ! [X0] : k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),X0)) = k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0)
    | ~ spl2_1 ),
    inference(superposition,[],[f50,f524])).

fof(f84,plain,
    ( k1_xboole_0 != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl2_2
  <=> k1_xboole_0 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f401,plain,
    ( spl2_1
    | ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f400])).

fof(f400,plain,
    ( $false
    | spl2_1
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f399,f33])).

fof(f399,plain,
    ( k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | spl2_1
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f393,f67])).

fof(f67,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f37,f61])).

fof(f37,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f393,plain,
    ( k1_xboole_0 != k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))))
    | spl2_1
    | ~ spl2_2 ),
    inference(superposition,[],[f74,f237])).

fof(f237,plain,
    ( k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | spl2_1
    | ~ spl2_2 ),
    inference(superposition,[],[f201,f35])).

fof(f201,plain,
    ( k1_xboole_0 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0)
    | spl2_1
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f200,f33])).

fof(f200,plain,
    ( k1_xboole_0 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,sK1))
    | spl2_1
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f197,f35])).

fof(f197,plain,
    ( k1_xboole_0 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k5_xboole_0(sK1,k1_xboole_0)))
    | spl2_1
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f147,f195])).

fof(f195,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | spl2_1
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f148,f194])).

fof(f194,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))))
    | spl2_1
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f193,f33])).

fof(f193,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) = k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | spl2_1
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f192,f33])).

fof(f192,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK1))
    | spl2_1
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f180,f35])).

fof(f180,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k5_xboole_0(sK1,k1_xboole_0)))
    | spl2_1
    | ~ spl2_2 ),
    inference(superposition,[],[f167,f103])).

fof(f103,plain,
    ( k1_xboole_0 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))))
    | spl2_1
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f83,f102])).

fof(f102,plain,
    ( k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) = k5_xboole_0(sK1,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | spl2_1 ),
    inference(forward_demodulation,[],[f97,f35])).

fof(f97,plain,
    ( k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0)))
    | spl2_1 ),
    inference(superposition,[],[f96,f33])).

fof(f96,plain,
    ( ! [X0] : k5_xboole_0(sK1,X0) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),X0))))
    | spl2_1 ),
    inference(forward_demodulation,[],[f95,f50])).

fof(f95,plain,
    ( ! [X0] : k5_xboole_0(sK1,X0) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),X0)))
    | spl2_1 ),
    inference(forward_demodulation,[],[f94,f50])).

fof(f94,plain,
    ( ! [X0] : k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))),X0)) = k5_xboole_0(sK1,X0)
    | spl2_1 ),
    inference(superposition,[],[f50,f90])).

fof(f90,plain,
    ( sK1 = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))))
    | spl2_1 ),
    inference(forward_demodulation,[],[f89,f50])).

fof(f89,plain,
    ( sK1 = k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))))
    | spl2_1 ),
    inference(resolution,[],[f80,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) = X0 ) ),
    inference(definition_unfolding,[],[f46,f62,f63])).

fof(f62,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f42,f61])).

fof(f42,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f80,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f78])).

fof(f83,plain,
    ( k1_xboole_0 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f82])).

fof(f167,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0))))
    | spl2_1
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f166,f50])).

fof(f166,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0)))
    | spl2_1
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f165,f50])).

fof(f165,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),X0))
    | spl2_1
    | ~ spl2_2 ),
    inference(superposition,[],[f50,f160])).

fof(f160,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
    | spl2_1
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f159,f33])).

fof(f159,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
    | spl2_1
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f157,f35])).

fof(f157,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0))
    | spl2_1
    | ~ spl2_2 ),
    inference(superposition,[],[f112,f124])).

fof(f124,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))))
    | spl2_1 ),
    inference(forward_demodulation,[],[f121,f33])).

fof(f121,plain,
    ( k5_xboole_0(sK1,sK1) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))))
    | spl2_1 ),
    inference(superposition,[],[f99,f102])).

fof(f99,plain,
    ( ! [X0] : k5_xboole_0(sK1,X0) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(X0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))))))
    | spl2_1 ),
    inference(superposition,[],[f96,f39])).

fof(f112,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0)))))
    | spl2_1
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f111,f50])).

fof(f111,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0))))
    | spl2_1
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f110,f50])).

fof(f110,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),X0)))
    | spl2_1
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f109,f50])).

fof(f109,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),X0))
    | spl2_1
    | ~ spl2_2 ),
    inference(superposition,[],[f50,f103])).

fof(f148,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) = k5_xboole_0(k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | spl2_1
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f142,f147])).

fof(f142,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))))
    | spl2_1
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f141,f50])).

fof(f141,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k1_xboole_0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
    | spl2_1
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f140,f50])).

fof(f140,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k1_xboole_0)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | spl2_1
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f129,f39])).

fof(f129,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k5_xboole_0(sK1,k1_xboole_0))))
    | spl2_1
    | ~ spl2_2 ),
    inference(superposition,[],[f112,f103])).

fof(f147,plain,
    ( k5_xboole_0(k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))))
    | spl2_1
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f146,f50])).

fof(f146,plain,
    ( k5_xboole_0(k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k1_xboole_0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
    | spl2_1
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f145,f50])).

fof(f145,plain,
    ( k5_xboole_0(k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k1_xboole_0)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | spl2_1
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f132,f39])).

fof(f132,plain,
    ( k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k5_xboole_0(sK1,k1_xboole_0)))) = k5_xboole_0(k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | spl2_1
    | ~ spl2_2 ),
    inference(superposition,[],[f112,f33])).

fof(f74,plain,(
    ! [X1] : k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) ) ),
    inference(definition_unfolding,[],[f47,f63,f62,f63,f63])).

fof(f47,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f88,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f87,f82,f78])).

fof(f87,plain,
    ( k1_xboole_0 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))))
    | r2_hidden(sK0,sK1) ),
    inference(forward_demodulation,[],[f86,f68])).

fof(f68,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f38,f59,f59])).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f86,plain,
    ( k1_xboole_0 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)))))
    | r2_hidden(sK0,sK1) ),
    inference(forward_demodulation,[],[f65,f50])).

fof(f65,plain,
    ( r2_hidden(sK0,sK1)
    | k1_xboole_0 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)))) ),
    inference(definition_unfolding,[],[f31,f62,f63])).

fof(f31,plain,
    ( r2_hidden(sK0,sK1)
    | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( ~ r2_hidden(sK0,sK1)
      | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) )
    & ( r2_hidden(sK0,sK1)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f27])).

fof(f27,plain,
    ( ? [X0,X1] :
        ( ( ~ r2_hidden(X0,X1)
          | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) )
        & ( r2_hidden(X0,X1)
          | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) )
   => ( ( ~ r2_hidden(sK0,sK1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) )
      & ( r2_hidden(sK0,sK1)
        | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ( ~ r2_hidden(X0,X1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) )
      & ( r2_hidden(X0,X1)
        | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <~> r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
      <=> r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_zfmisc_1)).

fof(f85,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f76,f82,f78])).

fof(f76,plain,
    ( k1_xboole_0 != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))))
    | ~ r2_hidden(sK0,sK1) ),
    inference(forward_demodulation,[],[f75,f68])).

fof(f75,plain,
    ( k1_xboole_0 != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)))))
    | ~ r2_hidden(sK0,sK1) ),
    inference(forward_demodulation,[],[f64,f50])).

fof(f64,plain,
    ( ~ r2_hidden(sK0,sK1)
    | k1_xboole_0 != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)))) ),
    inference(definition_unfolding,[],[f32,f62,f63])).

fof(f32,plain,
    ( ~ r2_hidden(sK0,sK1)
    | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:55:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.49  % (18410)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.49  % (18402)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.49  % (18402)Refutation not found, incomplete strategy% (18402)------------------------------
% 0.22/0.49  % (18402)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (18410)Refutation not found, incomplete strategy% (18410)------------------------------
% 0.22/0.49  % (18410)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (18402)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (18402)Memory used [KB]: 6140
% 0.22/0.49  % (18402)Time elapsed: 0.004 s
% 0.22/0.49  % (18402)------------------------------
% 0.22/0.49  % (18402)------------------------------
% 0.22/0.49  % (18410)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (18410)Memory used [KB]: 1663
% 0.22/0.49  % (18410)Time elapsed: 0.068 s
% 0.22/0.49  % (18410)------------------------------
% 0.22/0.49  % (18410)------------------------------
% 0.22/0.51  % (18390)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (18389)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (18406)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.53  % (18400)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.53  % (18396)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.53  % (18398)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.53  % (18404)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.54  % (18408)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.54  % (18387)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (18397)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.54  % (18404)Refutation not found, incomplete strategy% (18404)------------------------------
% 0.22/0.54  % (18404)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (18404)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (18404)Memory used [KB]: 10618
% 0.22/0.54  % (18404)Time elapsed: 0.118 s
% 0.22/0.54  % (18404)------------------------------
% 0.22/0.54  % (18404)------------------------------
% 0.22/0.54  % (18413)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (18414)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (18388)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (18416)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  % (18393)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (18392)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.55  % (18395)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.55  % (18405)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.55  % (18411)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.55  % (18398)Refutation not found, incomplete strategy% (18398)------------------------------
% 0.22/0.55  % (18398)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (18398)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (18398)Memory used [KB]: 10746
% 0.22/0.55  % (18398)Time elapsed: 0.132 s
% 0.22/0.55  % (18398)------------------------------
% 0.22/0.55  % (18398)------------------------------
% 0.22/0.56  % (18409)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.56  % (18394)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.56  % (18397)Refutation not found, incomplete strategy% (18397)------------------------------
% 0.22/0.56  % (18397)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (18397)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (18397)Memory used [KB]: 10746
% 0.22/0.56  % (18397)Time elapsed: 0.136 s
% 0.22/0.56  % (18397)------------------------------
% 0.22/0.56  % (18397)------------------------------
% 0.22/0.56  % (18403)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.56  % (18391)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.57  % (18415)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.57  % (18401)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.58  % (18407)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.58  % (18409)Refutation not found, incomplete strategy% (18409)------------------------------
% 0.22/0.58  % (18409)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (18407)Refutation not found, incomplete strategy% (18407)------------------------------
% 0.22/0.58  % (18407)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (18409)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  % (18407)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  
% 0.22/0.58  % (18409)Memory used [KB]: 10746
% 0.22/0.58  % (18407)Memory used [KB]: 10746
% 0.22/0.58  % (18409)Time elapsed: 0.170 s
% 0.22/0.58  % (18407)Time elapsed: 0.169 s
% 0.22/0.58  % (18409)------------------------------
% 0.22/0.58  % (18409)------------------------------
% 0.22/0.58  % (18407)------------------------------
% 0.22/0.58  % (18407)------------------------------
% 0.22/0.58  % (18412)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.58  % (18399)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.63/0.60  % (18395)Refutation found. Thanks to Tanya!
% 1.63/0.60  % SZS status Theorem for theBenchmark
% 1.63/0.60  % SZS output start Proof for theBenchmark
% 1.63/0.60  fof(f623,plain,(
% 1.63/0.60    $false),
% 1.63/0.60    inference(avatar_sat_refutation,[],[f85,f88,f401,f619])).
% 1.63/0.60  fof(f619,plain,(
% 1.63/0.60    ~spl2_1 | spl2_2),
% 1.63/0.60    inference(avatar_contradiction_clause,[],[f618])).
% 1.63/0.60  fof(f618,plain,(
% 1.63/0.60    $false | (~spl2_1 | spl2_2)),
% 1.63/0.60    inference(subsumption_resolution,[],[f617,f33])).
% 1.63/0.60  fof(f33,plain,(
% 1.63/0.60    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.63/0.60    inference(cnf_transformation,[],[f6])).
% 1.63/0.60  fof(f6,axiom,(
% 1.63/0.60    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.63/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.63/0.60  fof(f617,plain,(
% 1.63/0.60    k1_xboole_0 != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | (~spl2_1 | spl2_2)),
% 1.63/0.60    inference(forward_demodulation,[],[f616,f591])).
% 1.63/0.60  fof(f591,plain,(
% 1.63/0.60    ( ! [X5] : (k5_xboole_0(sK1,k5_xboole_0(X5,sK1)) = X5) ) | ~spl2_1),
% 1.63/0.60    inference(superposition,[],[f568,f39])).
% 1.63/0.60  fof(f39,plain,(
% 1.63/0.60    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.63/0.60    inference(cnf_transformation,[],[f1])).
% 1.63/0.60  fof(f1,axiom,(
% 1.63/0.60    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.63/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.63/0.60  fof(f568,plain,(
% 1.63/0.60    ( ! [X0] : (k5_xboole_0(sK1,k5_xboole_0(sK1,X0)) = X0) ) | ~spl2_1),
% 1.63/0.60    inference(forward_demodulation,[],[f555,f35])).
% 1.63/0.60  fof(f35,plain,(
% 1.63/0.60    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.63/0.60    inference(cnf_transformation,[],[f4])).
% 1.63/0.60  fof(f4,axiom,(
% 1.63/0.60    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.63/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.63/0.60  fof(f555,plain,(
% 1.63/0.60    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(X0,k1_xboole_0)))) ) | ~spl2_1),
% 1.63/0.60    inference(superposition,[],[f548,f33])).
% 1.63/0.60  fof(f548,plain,(
% 1.63/0.60    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X3,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(X2,k5_xboole_0(X3,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))))) ) | ~spl2_1),
% 1.63/0.60    inference(superposition,[],[f534,f50])).
% 1.63/0.60  fof(f50,plain,(
% 1.63/0.60    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.63/0.60    inference(cnf_transformation,[],[f5])).
% 1.63/0.60  fof(f5,axiom,(
% 1.63/0.60    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.63/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.63/0.60  fof(f534,plain,(
% 1.63/0.60    ( ! [X1] : (k5_xboole_0(X1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(X1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) ) | ~spl2_1),
% 1.63/0.60    inference(superposition,[],[f530,f39])).
% 1.63/0.60  fof(f530,plain,(
% 1.63/0.60    ( ! [X0] : (k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0)))) ) | ~spl2_1),
% 1.63/0.60    inference(forward_demodulation,[],[f529,f50])).
% 1.63/0.60  fof(f529,plain,(
% 1.63/0.60    ( ! [X0] : (k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0)) ) | ~spl2_1),
% 1.63/0.60    inference(superposition,[],[f50,f525])).
% 1.63/0.60  fof(f525,plain,(
% 1.63/0.60    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(sK1,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | ~spl2_1),
% 1.63/0.60    inference(backward_demodulation,[],[f440,f524])).
% 1.63/0.60  fof(f524,plain,(
% 1.63/0.60    k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) | ~spl2_1),
% 1.63/0.60    inference(forward_demodulation,[],[f517,f35])).
% 1.63/0.60  fof(f517,plain,(
% 1.63/0.60    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) = k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k1_xboole_0) | ~spl2_1),
% 1.63/0.60    inference(superposition,[],[f443,f33])).
% 1.63/0.60  fof(f443,plain,(
% 1.63/0.60    ( ! [X0] : (k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0) = k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k5_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),X0))) ) | ~spl2_1),
% 1.63/0.60    inference(superposition,[],[f50,f411])).
% 1.63/0.60  fof(f411,plain,(
% 1.63/0.60    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) | ~spl2_1),
% 1.63/0.60    inference(resolution,[],[f79,f69])).
% 1.63/0.60  fof(f69,plain,(
% 1.63/0.60    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k5_xboole_0(k5_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))) )),
% 1.63/0.60    inference(definition_unfolding,[],[f44,f63,f61,f63])).
% 1.63/0.60  fof(f61,plain,(
% 1.63/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.63/0.60    inference(definition_unfolding,[],[f43,f60])).
% 1.63/0.60  fof(f60,plain,(
% 1.63/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.63/0.60    inference(definition_unfolding,[],[f40,f59])).
% 1.63/0.60  fof(f59,plain,(
% 1.63/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.63/0.60    inference(definition_unfolding,[],[f41,f58])).
% 1.63/0.60  fof(f58,plain,(
% 1.63/0.60    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.63/0.60    inference(definition_unfolding,[],[f49,f57])).
% 1.63/0.60  fof(f57,plain,(
% 1.63/0.60    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.63/0.60    inference(definition_unfolding,[],[f51,f56])).
% 1.63/0.60  fof(f56,plain,(
% 1.63/0.60    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.63/0.60    inference(definition_unfolding,[],[f52,f55])).
% 1.63/0.60  fof(f55,plain,(
% 1.63/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.63/0.60    inference(definition_unfolding,[],[f53,f54])).
% 1.63/0.60  fof(f54,plain,(
% 1.63/0.60    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.63/0.60    inference(cnf_transformation,[],[f15])).
% 1.63/0.60  fof(f15,axiom,(
% 1.63/0.60    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.63/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 1.63/0.60  fof(f53,plain,(
% 1.63/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.63/0.60    inference(cnf_transformation,[],[f14])).
% 1.63/0.60  fof(f14,axiom,(
% 1.63/0.60    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.63/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.63/0.60  fof(f52,plain,(
% 1.63/0.60    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.63/0.60    inference(cnf_transformation,[],[f13])).
% 1.63/0.60  fof(f13,axiom,(
% 1.63/0.60    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.63/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.63/0.60  fof(f51,plain,(
% 1.63/0.60    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.63/0.60    inference(cnf_transformation,[],[f12])).
% 1.63/0.60  fof(f12,axiom,(
% 1.63/0.60    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.63/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.63/0.60  fof(f49,plain,(
% 1.63/0.60    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.63/0.60    inference(cnf_transformation,[],[f11])).
% 1.63/0.60  fof(f11,axiom,(
% 1.63/0.60    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.63/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.63/0.60  fof(f41,plain,(
% 1.63/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.63/0.60    inference(cnf_transformation,[],[f10])).
% 1.63/0.60  fof(f10,axiom,(
% 1.63/0.60    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.63/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.63/0.60  fof(f40,plain,(
% 1.63/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.63/0.60    inference(cnf_transformation,[],[f17])).
% 1.63/0.60  fof(f17,axiom,(
% 1.63/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.63/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.63/0.60  fof(f43,plain,(
% 1.63/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 1.63/0.60    inference(cnf_transformation,[],[f7])).
% 1.63/0.60  fof(f7,axiom,(
% 1.63/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 1.63/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 1.63/0.60  fof(f63,plain,(
% 1.63/0.60    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.63/0.60    inference(definition_unfolding,[],[f36,f59])).
% 1.63/0.60  fof(f36,plain,(
% 1.63/0.60    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.63/0.60    inference(cnf_transformation,[],[f9])).
% 1.63/0.60  fof(f9,axiom,(
% 1.63/0.60    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.63/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.63/0.60  fof(f44,plain,(
% 1.63/0.60    ( ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1)) )),
% 1.63/0.60    inference(cnf_transformation,[],[f25])).
% 1.63/0.60  fof(f25,plain,(
% 1.63/0.60    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1))),
% 1.63/0.60    inference(ennf_transformation,[],[f16])).
% 1.63/0.60  fof(f16,axiom,(
% 1.63/0.60    ! [X0,X1] : (r2_hidden(X0,X1) => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)))),
% 1.63/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).
% 1.63/0.60  fof(f79,plain,(
% 1.63/0.60    r2_hidden(sK0,sK1) | ~spl2_1),
% 1.63/0.60    inference(avatar_component_clause,[],[f78])).
% 1.63/0.60  fof(f78,plain,(
% 1.63/0.60    spl2_1 <=> r2_hidden(sK0,sK1)),
% 1.63/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.63/0.60  fof(f440,plain,(
% 1.63/0.60    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) | ~spl2_1),
% 1.63/0.60    inference(superposition,[],[f411,f50])).
% 1.63/0.60  fof(f616,plain,(
% 1.63/0.60    k1_xboole_0 != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) | (~spl2_1 | spl2_2)),
% 1.63/0.60    inference(backward_demodulation,[],[f84,f607])).
% 1.63/0.60  fof(f607,plain,(
% 1.63/0.60    ( ! [X0] : (k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(X0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) = k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0))) ) | ~spl2_1),
% 1.63/0.60    inference(superposition,[],[f543,f39])).
% 1.63/0.60  fof(f543,plain,(
% 1.63/0.60    ( ! [X0] : (k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),X0)) = k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0))) ) | ~spl2_1),
% 1.63/0.60    inference(forward_demodulation,[],[f542,f50])).
% 1.63/0.60  fof(f542,plain,(
% 1.63/0.60    ( ! [X0] : (k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),X0)) = k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0)) ) | ~spl2_1),
% 1.63/0.60    inference(superposition,[],[f50,f524])).
% 1.63/0.60  fof(f84,plain,(
% 1.63/0.60    k1_xboole_0 != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))))) | spl2_2),
% 1.63/0.60    inference(avatar_component_clause,[],[f82])).
% 1.63/0.60  fof(f82,plain,(
% 1.63/0.60    spl2_2 <=> k1_xboole_0 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))))),
% 1.63/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.63/0.60  fof(f401,plain,(
% 1.63/0.60    spl2_1 | ~spl2_2),
% 1.63/0.60    inference(avatar_contradiction_clause,[],[f400])).
% 1.63/0.60  fof(f400,plain,(
% 1.63/0.60    $false | (spl2_1 | ~spl2_2)),
% 1.63/0.60    inference(subsumption_resolution,[],[f399,f33])).
% 1.63/0.60  fof(f399,plain,(
% 1.63/0.60    k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_xboole_0) | (spl2_1 | ~spl2_2)),
% 1.63/0.60    inference(forward_demodulation,[],[f393,f67])).
% 1.63/0.60  fof(f67,plain,(
% 1.63/0.60    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0) )),
% 1.63/0.60    inference(definition_unfolding,[],[f37,f61])).
% 1.63/0.60  fof(f37,plain,(
% 1.63/0.60    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.63/0.60    inference(cnf_transformation,[],[f23])).
% 1.63/0.60  fof(f23,plain,(
% 1.63/0.60    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.63/0.60    inference(rectify,[],[f2])).
% 1.63/0.60  fof(f2,axiom,(
% 1.63/0.60    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.63/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.63/0.60  fof(f393,plain,(
% 1.63/0.60    k1_xboole_0 != k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))) | (spl2_1 | ~spl2_2)),
% 1.63/0.60    inference(superposition,[],[f74,f237])).
% 1.63/0.60  fof(f237,plain,(
% 1.63/0.60    k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | (spl2_1 | ~spl2_2)),
% 1.63/0.60    inference(superposition,[],[f201,f35])).
% 1.63/0.60  fof(f201,plain,(
% 1.63/0.60    k1_xboole_0 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0) | (spl2_1 | ~spl2_2)),
% 1.63/0.60    inference(forward_demodulation,[],[f200,f33])).
% 1.63/0.60  fof(f200,plain,(
% 1.63/0.60    k1_xboole_0 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,sK1)) | (spl2_1 | ~spl2_2)),
% 1.63/0.60    inference(forward_demodulation,[],[f197,f35])).
% 1.63/0.60  fof(f197,plain,(
% 1.63/0.60    k1_xboole_0 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k5_xboole_0(sK1,k1_xboole_0))) | (spl2_1 | ~spl2_2)),
% 1.63/0.60    inference(backward_demodulation,[],[f147,f195])).
% 1.63/0.60  fof(f195,plain,(
% 1.63/0.60    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | (spl2_1 | ~spl2_2)),
% 1.63/0.60    inference(backward_demodulation,[],[f148,f194])).
% 1.63/0.60  fof(f194,plain,(
% 1.63/0.60    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) | (spl2_1 | ~spl2_2)),
% 1.63/0.60    inference(forward_demodulation,[],[f193,f33])).
% 1.63/0.60  fof(f193,plain,(
% 1.63/0.60    k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) = k5_xboole_0(k1_xboole_0,k1_xboole_0) | (spl2_1 | ~spl2_2)),
% 1.63/0.60    inference(forward_demodulation,[],[f192,f33])).
% 1.63/0.60  fof(f192,plain,(
% 1.63/0.60    k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK1)) | (spl2_1 | ~spl2_2)),
% 1.63/0.60    inference(forward_demodulation,[],[f180,f35])).
% 1.63/0.60  fof(f180,plain,(
% 1.63/0.60    k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k5_xboole_0(sK1,k1_xboole_0))) | (spl2_1 | ~spl2_2)),
% 1.63/0.60    inference(superposition,[],[f167,f103])).
% 1.63/0.60  fof(f103,plain,(
% 1.63/0.60    k1_xboole_0 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) | (spl2_1 | ~spl2_2)),
% 1.63/0.60    inference(backward_demodulation,[],[f83,f102])).
% 1.63/0.60  fof(f102,plain,(
% 1.63/0.60    k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) = k5_xboole_0(sK1,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | spl2_1),
% 1.63/0.60    inference(forward_demodulation,[],[f97,f35])).
% 1.63/0.60  fof(f97,plain,(
% 1.63/0.60    k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0))) | spl2_1),
% 1.63/0.60    inference(superposition,[],[f96,f33])).
% 1.63/0.60  fof(f96,plain,(
% 1.63/0.60    ( ! [X0] : (k5_xboole_0(sK1,X0) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),X0))))) ) | spl2_1),
% 1.63/0.60    inference(forward_demodulation,[],[f95,f50])).
% 1.63/0.60  fof(f95,plain,(
% 1.63/0.60    ( ! [X0] : (k5_xboole_0(sK1,X0) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),X0)))) ) | spl2_1),
% 1.63/0.60    inference(forward_demodulation,[],[f94,f50])).
% 1.63/0.60  fof(f94,plain,(
% 1.63/0.60    ( ! [X0] : (k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))),X0)) = k5_xboole_0(sK1,X0)) ) | spl2_1),
% 1.63/0.60    inference(superposition,[],[f50,f90])).
% 1.63/0.60  fof(f90,plain,(
% 1.63/0.60    sK1 = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))))) | spl2_1),
% 1.63/0.60    inference(forward_demodulation,[],[f89,f50])).
% 1.63/0.60  fof(f89,plain,(
% 1.63/0.60    sK1 = k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) | spl2_1),
% 1.63/0.60    inference(resolution,[],[f80,f70])).
% 1.63/0.60  fof(f70,plain,(
% 1.63/0.60    ( ! [X0,X1] : (r2_hidden(X1,X0) | k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) = X0) )),
% 1.63/0.60    inference(definition_unfolding,[],[f46,f62,f63])).
% 1.63/0.60  fof(f62,plain,(
% 1.63/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 1.63/0.60    inference(definition_unfolding,[],[f42,f61])).
% 1.63/0.60  fof(f42,plain,(
% 1.63/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.63/0.60    inference(cnf_transformation,[],[f3])).
% 1.63/0.60  fof(f3,axiom,(
% 1.63/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.63/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.63/0.60  fof(f46,plain,(
% 1.63/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 1.63/0.60    inference(cnf_transformation,[],[f29])).
% 1.63/0.60  fof(f29,plain,(
% 1.63/0.60    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 1.63/0.60    inference(nnf_transformation,[],[f20])).
% 1.63/0.60  fof(f20,axiom,(
% 1.63/0.60    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.63/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 1.63/0.60  fof(f80,plain,(
% 1.63/0.60    ~r2_hidden(sK0,sK1) | spl2_1),
% 1.63/0.60    inference(avatar_component_clause,[],[f78])).
% 1.63/0.60  fof(f83,plain,(
% 1.63/0.60    k1_xboole_0 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))))) | ~spl2_2),
% 1.63/0.60    inference(avatar_component_clause,[],[f82])).
% 1.63/0.60  fof(f167,plain,(
% 1.63/0.60    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0))))) ) | (spl2_1 | ~spl2_2)),
% 1.63/0.60    inference(forward_demodulation,[],[f166,f50])).
% 1.63/0.60  fof(f166,plain,(
% 1.63/0.60    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0)))) ) | (spl2_1 | ~spl2_2)),
% 1.63/0.60    inference(forward_demodulation,[],[f165,f50])).
% 1.63/0.60  fof(f165,plain,(
% 1.63/0.60    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),X0))) ) | (spl2_1 | ~spl2_2)),
% 1.63/0.60    inference(superposition,[],[f50,f160])).
% 1.63/0.60  fof(f160,plain,(
% 1.63/0.60    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) | (spl2_1 | ~spl2_2)),
% 1.63/0.60    inference(forward_demodulation,[],[f159,f33])).
% 1.63/0.60  fof(f159,plain,(
% 1.63/0.60    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) | (spl2_1 | ~spl2_2)),
% 1.63/0.60    inference(forward_demodulation,[],[f157,f35])).
% 1.63/0.60  fof(f157,plain,(
% 1.63/0.60    k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0)) | (spl2_1 | ~spl2_2)),
% 1.63/0.60    inference(superposition,[],[f112,f124])).
% 1.63/0.60  fof(f124,plain,(
% 1.63/0.60    k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))))) | spl2_1),
% 1.63/0.60    inference(forward_demodulation,[],[f121,f33])).
% 1.63/0.60  fof(f121,plain,(
% 1.63/0.60    k5_xboole_0(sK1,sK1) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))))) | spl2_1),
% 1.63/0.60    inference(superposition,[],[f99,f102])).
% 1.63/0.60  fof(f99,plain,(
% 1.63/0.60    ( ! [X0] : (k5_xboole_0(sK1,X0) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(X0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))))))) ) | spl2_1),
% 1.63/0.60    inference(superposition,[],[f96,f39])).
% 1.63/0.60  fof(f112,plain,(
% 1.63/0.60    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X0)))))) ) | (spl2_1 | ~spl2_2)),
% 1.63/0.60    inference(forward_demodulation,[],[f111,f50])).
% 1.63/0.60  fof(f111,plain,(
% 1.63/0.60    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),X0))))) ) | (spl2_1 | ~spl2_2)),
% 1.63/0.60    inference(forward_demodulation,[],[f110,f50])).
% 1.63/0.60  fof(f110,plain,(
% 1.63/0.60    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),X0)))) ) | (spl2_1 | ~spl2_2)),
% 1.63/0.60    inference(forward_demodulation,[],[f109,f50])).
% 1.63/0.60  fof(f109,plain,(
% 1.63/0.60    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),X0))) ) | (spl2_1 | ~spl2_2)),
% 1.63/0.60    inference(superposition,[],[f50,f103])).
% 1.63/0.60  fof(f148,plain,(
% 1.63/0.60    k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) = k5_xboole_0(k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | (spl2_1 | ~spl2_2)),
% 1.63/0.60    inference(backward_demodulation,[],[f142,f147])).
% 1.63/0.60  fof(f142,plain,(
% 1.63/0.60    k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) | (spl2_1 | ~spl2_2)),
% 1.63/0.60    inference(forward_demodulation,[],[f141,f50])).
% 1.63/0.60  fof(f141,plain,(
% 1.63/0.60    k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k1_xboole_0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) | (spl2_1 | ~spl2_2)),
% 1.63/0.60    inference(forward_demodulation,[],[f140,f50])).
% 1.63/0.60  fof(f140,plain,(
% 1.63/0.60    k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k1_xboole_0)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | (spl2_1 | ~spl2_2)),
% 1.63/0.60    inference(forward_demodulation,[],[f129,f39])).
% 1.63/0.60  fof(f129,plain,(
% 1.63/0.60    k5_xboole_0(k1_xboole_0,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k5_xboole_0(sK1,k1_xboole_0)))) | (spl2_1 | ~spl2_2)),
% 1.63/0.60    inference(superposition,[],[f112,f103])).
% 1.63/0.60  fof(f147,plain,(
% 1.63/0.60    k5_xboole_0(k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) | (spl2_1 | ~spl2_2)),
% 1.63/0.60    inference(forward_demodulation,[],[f146,f50])).
% 1.63/0.60  fof(f146,plain,(
% 1.63/0.60    k5_xboole_0(k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k1_xboole_0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) | (spl2_1 | ~spl2_2)),
% 1.63/0.60    inference(forward_demodulation,[],[f145,f50])).
% 1.63/0.60  fof(f145,plain,(
% 1.63/0.60    k5_xboole_0(k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,k1_xboole_0)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | (spl2_1 | ~spl2_2)),
% 1.63/0.60    inference(forward_demodulation,[],[f132,f39])).
% 1.63/0.60  fof(f132,plain,(
% 1.63/0.60    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k5_xboole_0(sK1,k1_xboole_0)))) = k5_xboole_0(k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | (spl2_1 | ~spl2_2)),
% 1.63/0.60    inference(superposition,[],[f112,f33])).
% 1.63/0.60  fof(f74,plain,(
% 1.63/0.60    ( ! [X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))))) )),
% 1.63/0.60    inference(equality_resolution,[],[f73])).
% 1.63/0.60  fof(f73,plain,(
% 1.63/0.60    ( ! [X0,X1] : (X0 != X1 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))))) )),
% 1.63/0.60    inference(definition_unfolding,[],[f47,f63,f62,f63,f63])).
% 1.63/0.60  fof(f47,plain,(
% 1.63/0.60    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.63/0.60    inference(cnf_transformation,[],[f30])).
% 1.63/0.60  fof(f30,plain,(
% 1.63/0.60    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 1.63/0.60    inference(nnf_transformation,[],[f18])).
% 1.63/0.60  fof(f18,axiom,(
% 1.63/0.60    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 1.63/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 1.63/0.60  fof(f88,plain,(
% 1.63/0.60    spl2_1 | spl2_2),
% 1.63/0.60    inference(avatar_split_clause,[],[f87,f82,f78])).
% 1.63/0.60  fof(f87,plain,(
% 1.63/0.60    k1_xboole_0 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))))) | r2_hidden(sK0,sK1)),
% 1.63/0.60    inference(forward_demodulation,[],[f86,f68])).
% 1.63/0.60  fof(f68,plain,(
% 1.63/0.60    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) )),
% 1.63/0.60    inference(definition_unfolding,[],[f38,f59,f59])).
% 1.63/0.60  fof(f38,plain,(
% 1.63/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.63/0.60    inference(cnf_transformation,[],[f8])).
% 1.63/0.60  fof(f8,axiom,(
% 1.63/0.60    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.63/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.63/0.60  fof(f86,plain,(
% 1.63/0.60    k1_xboole_0 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))))) | r2_hidden(sK0,sK1)),
% 1.63/0.60    inference(forward_demodulation,[],[f65,f50])).
% 1.63/0.60  fof(f65,plain,(
% 1.63/0.60    r2_hidden(sK0,sK1) | k1_xboole_0 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))))),
% 1.63/0.60    inference(definition_unfolding,[],[f31,f62,f63])).
% 1.63/0.60  fof(f31,plain,(
% 1.63/0.60    r2_hidden(sK0,sK1) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)),
% 1.63/0.60    inference(cnf_transformation,[],[f28])).
% 1.63/0.60  fof(f28,plain,(
% 1.63/0.60    (~r2_hidden(sK0,sK1) | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)) & (r2_hidden(sK0,sK1) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1))),
% 1.63/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f27])).
% 1.63/0.60  fof(f27,plain,(
% 1.63/0.60    ? [X0,X1] : ((~r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)) & (r2_hidden(X0,X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1))) => ((~r2_hidden(sK0,sK1) | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)) & (r2_hidden(sK0,sK1) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)))),
% 1.63/0.60    introduced(choice_axiom,[])).
% 1.63/0.60  fof(f26,plain,(
% 1.63/0.60    ? [X0,X1] : ((~r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)) & (r2_hidden(X0,X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)))),
% 1.63/0.60    inference(nnf_transformation,[],[f24])).
% 1.63/0.60  fof(f24,plain,(
% 1.63/0.60    ? [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <~> r2_hidden(X0,X1))),
% 1.63/0.60    inference(ennf_transformation,[],[f22])).
% 1.63/0.60  fof(f22,negated_conjecture,(
% 1.63/0.60    ~! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.63/0.60    inference(negated_conjecture,[],[f21])).
% 1.63/0.60  fof(f21,conjecture,(
% 1.63/0.60    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.63/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_zfmisc_1)).
% 1.63/0.60  fof(f85,plain,(
% 1.63/0.60    ~spl2_1 | ~spl2_2),
% 1.63/0.60    inference(avatar_split_clause,[],[f76,f82,f78])).
% 1.63/0.60  fof(f76,plain,(
% 1.63/0.60    k1_xboole_0 != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))))) | ~r2_hidden(sK0,sK1)),
% 1.63/0.60    inference(forward_demodulation,[],[f75,f68])).
% 1.63/0.60  fof(f75,plain,(
% 1.63/0.60    k1_xboole_0 != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))))) | ~r2_hidden(sK0,sK1)),
% 1.63/0.60    inference(forward_demodulation,[],[f64,f50])).
% 1.63/0.60  fof(f64,plain,(
% 1.63/0.60    ~r2_hidden(sK0,sK1) | k1_xboole_0 != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))))),
% 1.63/0.60    inference(definition_unfolding,[],[f32,f62,f63])).
% 1.63/0.60  fof(f32,plain,(
% 1.63/0.60    ~r2_hidden(sK0,sK1) | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)),
% 1.63/0.60    inference(cnf_transformation,[],[f28])).
% 1.63/0.60  % SZS output end Proof for theBenchmark
% 1.63/0.60  % (18395)------------------------------
% 1.63/0.60  % (18395)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.60  % (18395)Termination reason: Refutation
% 1.63/0.60  
% 1.63/0.60  % (18395)Memory used [KB]: 11129
% 1.63/0.60  % (18395)Time elapsed: 0.175 s
% 1.63/0.60  % (18395)------------------------------
% 1.63/0.60  % (18395)------------------------------
% 1.63/0.61  % (18386)Success in time 0.238 s
%------------------------------------------------------------------------------
