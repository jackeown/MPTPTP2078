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
% DateTime   : Thu Dec  3 12:40:34 EST 2020

% Result     : Theorem 1.35s
% Output     : Refutation 1.35s
% Verified   : 
% Statistics : Number of formulae       :   97 (2629 expanded)
%              Number of leaves         :   15 ( 816 expanded)
%              Depth                    :   35
%              Number of atoms          :  190 (3834 expanded)
%              Number of equality atoms :   69 (2160 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f380,plain,(
    $false ),
    inference(subsumption_resolution,[],[f379,f95])).

fof(f95,plain,(
    ! [X2] : r2_hidden(X2,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) != X1 ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f35,f71])).

fof(f71,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f29,f67])).

fof(f67,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f32,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f39,f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f51,f64])).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f60,f63])).

fof(f63,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f61,f62])).

fof(f62,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f61,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f39,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f32,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f29,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f379,plain,(
    ~ r2_hidden(sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(subsumption_resolution,[],[f359,f291])).

fof(f291,plain,(
    r2_hidden(sK0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) ),
    inference(backward_demodulation,[],[f176,f286])).

fof(f286,plain,(
    sK0 = sK2 ),
    inference(subsumption_resolution,[],[f285,f93])).

fof(f93,plain,(
    ! [X2,X0] :
      ( X0 = X2
      | ~ r2_hidden(X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f36,f71])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f285,plain,
    ( sK0 = sK2
    | r2_hidden(sK0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(subsumption_resolution,[],[f264,f176])).

fof(f264,plain,
    ( sK0 = sK2
    | ~ r2_hidden(sK0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))
    | r2_hidden(sK0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(resolution,[],[f262,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | r2_hidden(X0,X1)
      | r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f262,plain,
    ( ~ r2_hidden(sK0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))
    | sK0 = sK2 ),
    inference(subsumption_resolution,[],[f242,f210])).

fof(f210,plain,(
    r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f190,f177])).

fof(f177,plain,
    ( ~ r2_hidden(sK0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f155,f176])).

fof(f155,plain,
    ( r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))
    | ~ r2_hidden(sK0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(resolution,[],[f153,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f153,plain,
    ( r2_hidden(sK0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))
    | r2_hidden(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f132])).

fof(f132,plain,
    ( r2_hidden(sK0,sK1)
    | r2_hidden(sK0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))
    | r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f131,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f131,plain,
    ( r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))))
    | r2_hidden(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f110])).

fof(f110,plain,
    ( r2_hidden(sK0,sK1)
    | r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))))
    | r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f108,f47])).

fof(f108,plain,
    ( r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))))
    | r2_hidden(sK0,sK1) ),
    inference(forward_demodulation,[],[f73,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f73,plain,
    ( r2_hidden(sK0,sK1)
    | r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))) ),
    inference(definition_unfolding,[],[f25,f70,f71])).

fof(f70,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f33,f69])).

fof(f69,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f34,f68])).

fof(f68,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f31,f67])).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f25,plain,
    ( r2_hidden(sK0,sK1)
    | r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2))) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <~> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
      <=> ( X0 != X2
          & r2_hidden(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f190,plain,
    ( r2_hidden(sK0,sK1)
    | r2_hidden(sK0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(resolution,[],[f176,f98])).

fof(f98,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f44,f68])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f242,plain,
    ( sK0 = sK2
    | ~ r2_hidden(sK0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))
    | ~ r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f240,f48])).

fof(f240,plain,
    ( r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))))
    | sK0 = sK2 ),
    inference(subsumption_resolution,[],[f239,f210])).

fof(f239,plain,
    ( ~ r2_hidden(sK0,sK1)
    | sK0 = sK2
    | r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))) ),
    inference(duplicate_literal_removal,[],[f219])).

fof(f219,plain,
    ( ~ r2_hidden(sK0,sK1)
    | sK0 = sK2
    | r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))))
    | ~ r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f109,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1)
      | r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f109,plain,
    ( ~ r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))))
    | ~ r2_hidden(sK0,sK1)
    | sK0 = sK2 ),
    inference(forward_demodulation,[],[f74,f40])).

fof(f74,plain,
    ( ~ r2_hidden(sK0,sK1)
    | sK0 = sK2
    | ~ r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))) ),
    inference(definition_unfolding,[],[f24,f70,f71])).

fof(f24,plain,
    ( ~ r2_hidden(sK0,sK1)
    | sK0 = sK2
    | ~ r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2))) ),
    inference(cnf_transformation,[],[f21])).

fof(f176,plain,(
    r2_hidden(sK0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) ),
    inference(subsumption_resolution,[],[f175,f97])).

fof(f97,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X2)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f45,f68])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f175,plain,
    ( r2_hidden(sK0,sK1)
    | r2_hidden(sK0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) ),
    inference(subsumption_resolution,[],[f154,f96])).

fof(f96,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f46,f68])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f154,plain,
    ( r2_hidden(sK0,sK1)
    | r2_hidden(sK0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))
    | r2_hidden(sK0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(resolution,[],[f153,f47])).

fof(f359,plain,
    ( ~ r2_hidden(sK0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
    | ~ r2_hidden(sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(resolution,[],[f357,f48])).

fof(f357,plain,(
    r2_hidden(sK0,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) ),
    inference(subsumption_resolution,[],[f337,f210])).

fof(f337,plain,
    ( r2_hidden(sK0,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))))
    | ~ r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f335,f50])).

fof(f335,plain,(
    ~ r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))))) ),
    inference(subsumption_resolution,[],[f315,f210])).

fof(f315,plain,
    ( ~ r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))))
    | ~ r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f293,f48])).

fof(f293,plain,(
    r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))))) ),
    inference(trivial_inequality_removal,[],[f287])).

fof(f287,plain,
    ( sK0 != sK0
    | r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))))) ),
    inference(backward_demodulation,[],[f107,f286])).

fof(f107,plain,
    ( sK0 != sK2
    | r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))))) ),
    inference(inner_rewriting,[],[f106])).

fof(f106,plain,
    ( r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))))
    | sK0 != sK2 ),
    inference(forward_demodulation,[],[f72,f40])).

fof(f72,plain,
    ( sK0 != sK2
    | r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))) ),
    inference(definition_unfolding,[],[f26,f70,f71])).

fof(f26,plain,
    ( sK0 != sK2
    | r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2))) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n014.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 18:57:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.51  % (30616)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.51  % (30615)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.51  % (30614)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (30617)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (30619)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (30640)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.22/0.53  % (30631)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.22/0.53  % (30641)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.22/0.53  % (30627)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.22/0.53  % (30624)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.22/0.53  % (30637)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.22/0.53  % (30625)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.22/0.53  % (30634)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.22/0.53  % (30629)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.22/0.53  % (30620)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.22/0.53  % (30639)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.22/0.54  % (30614)Refutation not found, incomplete strategy% (30614)------------------------------
% 1.22/0.54  % (30614)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.54  % (30614)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.54  
% 1.22/0.54  % (30614)Memory used [KB]: 1791
% 1.22/0.54  % (30614)Time elapsed: 0.123 s
% 1.22/0.54  % (30614)------------------------------
% 1.22/0.54  % (30614)------------------------------
% 1.22/0.54  % (30626)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.35/0.54  % (30635)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.35/0.54  % (30643)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.35/0.54  % (30623)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.35/0.54  % (30631)Refutation found. Thanks to Tanya!
% 1.35/0.54  % SZS status Theorem for theBenchmark
% 1.35/0.54  % SZS output start Proof for theBenchmark
% 1.35/0.54  fof(f380,plain,(
% 1.35/0.54    $false),
% 1.35/0.54    inference(subsumption_resolution,[],[f379,f95])).
% 1.35/0.54  fof(f95,plain,(
% 1.35/0.54    ( ! [X2] : (r2_hidden(X2,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))) )),
% 1.35/0.54    inference(equality_resolution,[],[f94])).
% 1.35/0.54  fof(f94,plain,(
% 1.35/0.54    ( ! [X2,X1] : (r2_hidden(X2,X1) | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) != X1) )),
% 1.35/0.54    inference(equality_resolution,[],[f78])).
% 1.35/0.54  fof(f78,plain,(
% 1.35/0.54    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 1.35/0.54    inference(definition_unfolding,[],[f35,f71])).
% 1.35/0.54  fof(f71,plain,(
% 1.35/0.54    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.35/0.54    inference(definition_unfolding,[],[f29,f67])).
% 1.35/0.54  fof(f67,plain,(
% 1.35/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.35/0.54    inference(definition_unfolding,[],[f32,f66])).
% 1.35/0.54  fof(f66,plain,(
% 1.35/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.35/0.54    inference(definition_unfolding,[],[f39,f65])).
% 1.35/0.54  fof(f65,plain,(
% 1.35/0.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.35/0.54    inference(definition_unfolding,[],[f51,f64])).
% 1.35/0.54  fof(f64,plain,(
% 1.35/0.54    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.35/0.54    inference(definition_unfolding,[],[f60,f63])).
% 1.35/0.54  fof(f63,plain,(
% 1.35/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.35/0.54    inference(definition_unfolding,[],[f61,f62])).
% 1.35/0.54  fof(f62,plain,(
% 1.35/0.54    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f17])).
% 1.35/0.54  fof(f17,axiom,(
% 1.35/0.54    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 1.35/0.54  fof(f61,plain,(
% 1.35/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f16])).
% 1.35/0.54  fof(f16,axiom,(
% 1.35/0.54    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.35/0.54  fof(f60,plain,(
% 1.35/0.54    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f15])).
% 1.35/0.54  fof(f15,axiom,(
% 1.35/0.54    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.35/0.54  fof(f51,plain,(
% 1.35/0.54    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f14])).
% 1.35/0.54  fof(f14,axiom,(
% 1.35/0.54    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.35/0.54  fof(f39,plain,(
% 1.35/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f13])).
% 1.35/0.54  fof(f13,axiom,(
% 1.35/0.54    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.35/0.54  fof(f32,plain,(
% 1.35/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f12])).
% 1.35/0.54  fof(f12,axiom,(
% 1.35/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.35/0.54  fof(f29,plain,(
% 1.35/0.54    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f11])).
% 1.35/0.54  fof(f11,axiom,(
% 1.35/0.54    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.35/0.54  fof(f35,plain,(
% 1.35/0.54    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 1.35/0.54    inference(cnf_transformation,[],[f10])).
% 1.35/0.54  fof(f10,axiom,(
% 1.35/0.54    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.35/0.54  fof(f379,plain,(
% 1.35/0.54    ~r2_hidden(sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 1.35/0.54    inference(subsumption_resolution,[],[f359,f291])).
% 1.35/0.54  fof(f291,plain,(
% 1.35/0.54    r2_hidden(sK0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))),
% 1.35/0.54    inference(backward_demodulation,[],[f176,f286])).
% 1.35/0.54  fof(f286,plain,(
% 1.35/0.54    sK0 = sK2),
% 1.35/0.54    inference(subsumption_resolution,[],[f285,f93])).
% 1.35/0.54  fof(f93,plain,(
% 1.35/0.54    ( ! [X2,X0] : (X0 = X2 | ~r2_hidden(X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) )),
% 1.35/0.54    inference(equality_resolution,[],[f77])).
% 1.35/0.54  fof(f77,plain,(
% 1.35/0.54    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 1.35/0.54    inference(definition_unfolding,[],[f36,f71])).
% 1.35/0.54  fof(f36,plain,(
% 1.35/0.54    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 1.35/0.54    inference(cnf_transformation,[],[f10])).
% 1.35/0.54  fof(f285,plain,(
% 1.35/0.54    sK0 = sK2 | r2_hidden(sK0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),
% 1.35/0.54    inference(subsumption_resolution,[],[f264,f176])).
% 1.35/0.54  fof(f264,plain,(
% 1.35/0.54    sK0 = sK2 | ~r2_hidden(sK0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) | r2_hidden(sK0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),
% 1.35/0.54    inference(resolution,[],[f262,f49])).
% 1.35/0.54  fof(f49,plain,(
% 1.35/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | r2_hidden(X0,X1) | r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 1.35/0.54    inference(cnf_transformation,[],[f22])).
% 1.35/0.54  fof(f22,plain,(
% 1.35/0.54    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 1.35/0.54    inference(ennf_transformation,[],[f3])).
% 1.35/0.54  fof(f3,axiom,(
% 1.35/0.54    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).
% 1.35/0.54  fof(f262,plain,(
% 1.35/0.54    ~r2_hidden(sK0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))) | sK0 = sK2),
% 1.35/0.54    inference(subsumption_resolution,[],[f242,f210])).
% 1.35/0.54  fof(f210,plain,(
% 1.35/0.54    r2_hidden(sK0,sK1)),
% 1.35/0.54    inference(subsumption_resolution,[],[f190,f177])).
% 1.35/0.54  fof(f177,plain,(
% 1.35/0.54    ~r2_hidden(sK0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | r2_hidden(sK0,sK1)),
% 1.35/0.54    inference(subsumption_resolution,[],[f155,f176])).
% 1.35/0.54  fof(f155,plain,(
% 1.35/0.54    r2_hidden(sK0,sK1) | ~r2_hidden(sK0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) | ~r2_hidden(sK0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),
% 1.35/0.54    inference(resolution,[],[f153,f48])).
% 1.35/0.54  fof(f48,plain,(
% 1.35/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 1.35/0.54    inference(cnf_transformation,[],[f22])).
% 1.35/0.54  fof(f153,plain,(
% 1.35/0.54    r2_hidden(sK0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))) | r2_hidden(sK0,sK1)),
% 1.35/0.54    inference(duplicate_literal_removal,[],[f132])).
% 1.35/0.54  fof(f132,plain,(
% 1.35/0.54    r2_hidden(sK0,sK1) | r2_hidden(sK0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))) | r2_hidden(sK0,sK1)),
% 1.35/0.54    inference(resolution,[],[f131,f47])).
% 1.35/0.54  fof(f47,plain,(
% 1.35/0.54    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | r2_hidden(X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 1.35/0.54    inference(cnf_transformation,[],[f22])).
% 1.35/0.54  fof(f131,plain,(
% 1.35/0.54    r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))) | r2_hidden(sK0,sK1)),
% 1.35/0.54    inference(duplicate_literal_removal,[],[f110])).
% 1.35/0.54  fof(f110,plain,(
% 1.35/0.54    r2_hidden(sK0,sK1) | r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))) | r2_hidden(sK0,sK1)),
% 1.35/0.54    inference(resolution,[],[f108,f47])).
% 1.35/0.54  fof(f108,plain,(
% 1.35/0.54    r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))))) | r2_hidden(sK0,sK1)),
% 1.35/0.54    inference(forward_demodulation,[],[f73,f40])).
% 1.35/0.54  fof(f40,plain,(
% 1.35/0.54    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.35/0.54    inference(cnf_transformation,[],[f6])).
% 1.35/0.54  fof(f6,axiom,(
% 1.35/0.54    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.35/0.54  fof(f73,plain,(
% 1.35/0.54    r2_hidden(sK0,sK1) | r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))))),
% 1.35/0.54    inference(definition_unfolding,[],[f25,f70,f71])).
% 1.35/0.54  fof(f70,plain,(
% 1.35/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 1.35/0.54    inference(definition_unfolding,[],[f33,f69])).
% 1.35/0.54  fof(f69,plain,(
% 1.35/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.35/0.54    inference(definition_unfolding,[],[f34,f68])).
% 1.35/0.54  fof(f68,plain,(
% 1.35/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.35/0.54    inference(definition_unfolding,[],[f31,f67])).
% 1.35/0.54  fof(f31,plain,(
% 1.35/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.35/0.54    inference(cnf_transformation,[],[f18])).
% 1.35/0.54  fof(f18,axiom,(
% 1.35/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.35/0.54  fof(f34,plain,(
% 1.35/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 1.35/0.54    inference(cnf_transformation,[],[f8])).
% 1.35/0.54  fof(f8,axiom,(
% 1.35/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 1.35/0.54  fof(f33,plain,(
% 1.35/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.35/0.54    inference(cnf_transformation,[],[f4])).
% 1.35/0.54  fof(f4,axiom,(
% 1.35/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.35/0.54  fof(f25,plain,(
% 1.35/0.54    r2_hidden(sK0,sK1) | r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2)))),
% 1.35/0.54    inference(cnf_transformation,[],[f21])).
% 1.35/0.54  fof(f21,plain,(
% 1.35/0.54    ? [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <~> (X0 != X2 & r2_hidden(X0,X1)))),
% 1.35/0.54    inference(ennf_transformation,[],[f20])).
% 1.35/0.54  fof(f20,negated_conjecture,(
% 1.35/0.54    ~! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 1.35/0.54    inference(negated_conjecture,[],[f19])).
% 1.35/0.54  fof(f19,conjecture,(
% 1.35/0.54    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 1.35/0.54  fof(f190,plain,(
% 1.35/0.54    r2_hidden(sK0,sK1) | r2_hidden(sK0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),
% 1.35/0.54    inference(resolution,[],[f176,f98])).
% 1.35/0.54  fof(f98,plain,(
% 1.35/0.54    ( ! [X0,X3,X1] : (r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.35/0.54    inference(equality_resolution,[],[f81])).
% 1.35/0.54  fof(f81,plain,(
% 1.35/0.54    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 1.35/0.54    inference(definition_unfolding,[],[f44,f68])).
% 1.35/0.54  fof(f44,plain,(
% 1.35/0.54    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.35/0.54    inference(cnf_transformation,[],[f2])).
% 1.35/0.54  fof(f2,axiom,(
% 1.35/0.54    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 1.35/0.54  fof(f242,plain,(
% 1.35/0.54    sK0 = sK2 | ~r2_hidden(sK0,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))) | ~r2_hidden(sK0,sK1)),
% 1.35/0.54    inference(resolution,[],[f240,f48])).
% 1.35/0.54  fof(f240,plain,(
% 1.35/0.54    r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))) | sK0 = sK2),
% 1.35/0.54    inference(subsumption_resolution,[],[f239,f210])).
% 1.35/0.54  fof(f239,plain,(
% 1.35/0.54    ~r2_hidden(sK0,sK1) | sK0 = sK2 | r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))))),
% 1.35/0.54    inference(duplicate_literal_removal,[],[f219])).
% 1.35/0.54  fof(f219,plain,(
% 1.35/0.54    ~r2_hidden(sK0,sK1) | sK0 = sK2 | r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))))) | ~r2_hidden(sK0,sK1)),
% 1.35/0.54    inference(resolution,[],[f109,f50])).
% 1.35/0.54  fof(f50,plain,(
% 1.35/0.54    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r2_hidden(X0,X1) | r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 1.35/0.54    inference(cnf_transformation,[],[f22])).
% 1.35/0.54  fof(f109,plain,(
% 1.35/0.54    ~r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))))) | ~r2_hidden(sK0,sK1) | sK0 = sK2),
% 1.35/0.54    inference(forward_demodulation,[],[f74,f40])).
% 1.35/0.54  fof(f74,plain,(
% 1.35/0.54    ~r2_hidden(sK0,sK1) | sK0 = sK2 | ~r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))))),
% 1.35/0.54    inference(definition_unfolding,[],[f24,f70,f71])).
% 1.35/0.54  fof(f24,plain,(
% 1.35/0.54    ~r2_hidden(sK0,sK1) | sK0 = sK2 | ~r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2)))),
% 1.35/0.54    inference(cnf_transformation,[],[f21])).
% 1.35/0.54  fof(f176,plain,(
% 1.35/0.54    r2_hidden(sK0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))),
% 1.35/0.54    inference(subsumption_resolution,[],[f175,f97])).
% 1.35/0.54  fof(f97,plain,(
% 1.35/0.54    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.35/0.54    inference(equality_resolution,[],[f80])).
% 1.35/0.54  fof(f80,plain,(
% 1.35/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X2) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 1.35/0.54    inference(definition_unfolding,[],[f45,f68])).
% 1.35/0.54  fof(f45,plain,(
% 1.35/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.35/0.54    inference(cnf_transformation,[],[f2])).
% 1.35/0.54  fof(f175,plain,(
% 1.35/0.54    r2_hidden(sK0,sK1) | r2_hidden(sK0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))),
% 1.35/0.54    inference(subsumption_resolution,[],[f154,f96])).
% 1.35/0.54  fof(f96,plain,(
% 1.35/0.54    ( ! [X0,X3,X1] : (~r2_hidden(X3,X1) | r2_hidden(X3,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.35/0.54    inference(equality_resolution,[],[f79])).
% 1.35/0.54  fof(f79,plain,(
% 1.35/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | r2_hidden(X3,X2) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 1.35/0.54    inference(definition_unfolding,[],[f46,f68])).
% 1.35/0.54  fof(f46,plain,(
% 1.35/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.35/0.54    inference(cnf_transformation,[],[f2])).
% 1.35/0.54  fof(f154,plain,(
% 1.35/0.54    r2_hidden(sK0,sK1) | r2_hidden(sK0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) | r2_hidden(sK0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),
% 1.35/0.54    inference(resolution,[],[f153,f47])).
% 1.35/0.54  fof(f359,plain,(
% 1.35/0.54    ~r2_hidden(sK0,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) | ~r2_hidden(sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 1.35/0.54    inference(resolution,[],[f357,f48])).
% 1.35/0.54  fof(f357,plain,(
% 1.35/0.54    r2_hidden(sK0,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))))),
% 1.35/0.54    inference(subsumption_resolution,[],[f337,f210])).
% 1.35/0.54  fof(f337,plain,(
% 1.35/0.54    r2_hidden(sK0,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) | ~r2_hidden(sK0,sK1)),
% 1.35/0.54    inference(resolution,[],[f335,f50])).
% 1.35/0.54  fof(f335,plain,(
% 1.35/0.54    ~r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))))),
% 1.35/0.54    inference(subsumption_resolution,[],[f315,f210])).
% 1.35/0.54  fof(f315,plain,(
% 1.35/0.54    ~r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))))) | ~r2_hidden(sK0,sK1)),
% 1.35/0.54    inference(resolution,[],[f293,f48])).
% 1.35/0.54  fof(f293,plain,(
% 1.35/0.54    r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))))))),
% 1.35/0.54    inference(trivial_inequality_removal,[],[f287])).
% 1.35/0.54  fof(f287,plain,(
% 1.35/0.54    sK0 != sK0 | r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))))))),
% 1.35/0.54    inference(backward_demodulation,[],[f107,f286])).
% 1.35/0.54  fof(f107,plain,(
% 1.35/0.54    sK0 != sK2 | r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))))))),
% 1.35/0.54    inference(inner_rewriting,[],[f106])).
% 1.35/0.54  fof(f106,plain,(
% 1.35/0.54    r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))))) | sK0 != sK2),
% 1.35/0.54    inference(forward_demodulation,[],[f72,f40])).
% 1.35/0.54  fof(f72,plain,(
% 1.35/0.54    sK0 != sK2 | r2_hidden(sK0,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))))),
% 1.35/0.54    inference(definition_unfolding,[],[f26,f70,f71])).
% 1.35/0.54  fof(f26,plain,(
% 1.35/0.54    sK0 != sK2 | r2_hidden(sK0,k4_xboole_0(sK1,k1_tarski(sK2)))),
% 1.35/0.54    inference(cnf_transformation,[],[f21])).
% 1.35/0.54  % SZS output end Proof for theBenchmark
% 1.35/0.54  % (30631)------------------------------
% 1.35/0.54  % (30631)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (30631)Termination reason: Refutation
% 1.35/0.54  
% 1.35/0.54  % (30631)Memory used [KB]: 1791
% 1.35/0.54  % (30631)Time elapsed: 0.119 s
% 1.35/0.54  % (30631)------------------------------
% 1.35/0.54  % (30631)------------------------------
% 1.35/0.55  % (30613)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.35/0.55  % (30610)Success in time 0.18 s
%------------------------------------------------------------------------------
