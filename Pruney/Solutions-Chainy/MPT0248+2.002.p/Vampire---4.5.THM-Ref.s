%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:49 EST 2020

% Result     : Theorem 1.60s
% Output     : Refutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :  119 (46670 expanded)
%              Number of leaves         :   13 (14612 expanded)
%              Depth                    :   36
%              Number of atoms          :  246 (76015 expanded)
%              Number of equality atoms :  167 (57698 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f630,plain,(
    $false ),
    inference(subsumption_resolution,[],[f629,f436])).

fof(f436,plain,(
    sK1 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(trivial_inequality_removal,[],[f379])).

fof(f379,plain,
    ( k1_xboole_0 != k1_xboole_0
    | sK1 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(backward_demodulation,[],[f58,f376])).

fof(f376,plain,(
    k1_xboole_0 = sK2 ),
    inference(global_subsumption,[],[f76,f341,f375])).

fof(f375,plain,
    ( sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 = sK2 ),
    inference(forward_demodulation,[],[f342,f124])).

fof(f124,plain,(
    ! [X0] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X0)) = X0 ),
    inference(resolution,[],[f63,f71])).

fof(f71,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X1 ) ),
    inference(definition_unfolding,[],[f35,f53])).

fof(f53,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f32,f52])).

fof(f52,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f31,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f46,f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f46,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f31,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f342,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f55,f341])).

fof(f55,plain,(
    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f26,f54,f53])).

fof(f54,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f27,f52])).

fof(f27,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f26,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f341,plain,
    ( sK1 = sK2
    | k1_xboole_0 = sK2 ),
    inference(global_subsumption,[],[f214,f287,f340])).

fof(f340,plain,
    ( r1_tarski(sK2,sK1)
    | sK1 = sK2
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f338,f297])).

fof(f297,plain,
    ( r2_hidden(sK0,sK1)
    | sK1 = sK2 ),
    inference(global_subsumption,[],[f57,f101,f296])).

fof(f296,plain,
    ( sK2 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | r2_hidden(sK0,sK1)
    | sK1 = sK2 ),
    inference(forward_demodulation,[],[f291,f55])).

fof(f291,plain,
    ( r2_hidden(sK0,sK1)
    | sK1 = sK2
    | sK2 = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2)) ),
    inference(resolution,[],[f282,f63])).

fof(f282,plain,
    ( r1_tarski(sK1,sK2)
    | r2_hidden(sK0,sK1)
    | sK1 = sK2 ),
    inference(superposition,[],[f40,f279])).

fof(f279,plain,
    ( sK0 = sK4(sK1,sK2)
    | sK1 = sK2 ),
    inference(global_subsumption,[],[f101,f144,f278])).

fof(f278,plain,
    ( ~ r2_hidden(sK0,sK1)
    | sK0 = sK4(sK1,sK2)
    | sK1 = sK2 ),
    inference(subsumption_resolution,[],[f276,f104])).

fof(f104,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,sK1)
      | sK0 = sK4(sK1,X2)
      | sK1 = X2 ) ),
    inference(resolution,[],[f99,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f99,plain,(
    ! [X0] :
      ( r1_tarski(sK1,X0)
      | sK0 = sK4(sK1,X0) ) ),
    inference(resolution,[],[f94,f40])).

fof(f94,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK1)
      | sK0 = X2 ) ),
    inference(resolution,[],[f73,f85])).

fof(f85,plain,(
    ! [X0] :
      ( r2_hidden(X0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f84,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f84,plain,(
    r1_tarski(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f59,f55])).

fof(f59,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f29,f53])).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f73,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k3_enumset1(X0,X0,X0,X0,X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f43,f54])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f276,plain,
    ( ~ r2_hidden(sK0,sK1)
    | r1_tarski(sK2,sK1)
    | sK0 = sK4(sK1,sK2)
    | sK1 = sK2 ),
    inference(superposition,[],[f41,f222])).

fof(f222,plain,
    ( sK0 = sK4(sK2,sK1)
    | sK0 = sK4(sK1,sK2)
    | sK1 = sK2 ),
    inference(resolution,[],[f210,f104])).

fof(f210,plain,(
    ! [X0] :
      ( r1_tarski(sK2,X0)
      | sK0 = sK4(sK2,X0) ) ),
    inference(resolution,[],[f205,f40])).

fof(f205,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK2)
      | sK0 = X1 ) ),
    inference(resolution,[],[f201,f73])).

fof(f201,plain,(
    ! [X0] :
      ( r2_hidden(X0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
      | ~ r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f196,f39])).

fof(f196,plain,(
    r1_tarski(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f151,f55])).

fof(f151,plain,(
    ! [X4,X5] : r1_tarski(X4,k3_tarski(k3_enumset1(X5,X5,X5,X5,X4))) ),
    inference(superposition,[],[f59,f60])).

fof(f60,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f30,f52,f52])).

fof(f30,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f144,plain,
    ( k1_xboole_0 != sK1
    | sK0 = sK4(sK1,sK2) ),
    inference(trivial_inequality_removal,[],[f135])).

fof(f135,plain,
    ( sK2 != sK2
    | k1_xboole_0 != sK1
    | sK0 = sK4(sK1,sK2) ),
    inference(superposition,[],[f57,f129])).

fof(f129,plain,
    ( sK2 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | sK0 = sK4(sK1,sK2) ),
    inference(superposition,[],[f127,f55])).

fof(f127,plain,(
    ! [X3] :
      ( k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,X3)) = X3
      | sK0 = sK4(sK1,X3) ) ),
    inference(resolution,[],[f63,f99])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f101,plain,
    ( r2_hidden(sK0,sK1)
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f100])).

fof(f100,plain,
    ( r2_hidden(sK0,sK1)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f28,f98])).

fof(f98,plain,
    ( sK0 = sK3(sK1)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f94,f28])).

fof(f28,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f57,plain,
    ( sK2 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 != sK1 ),
    inference(definition_unfolding,[],[f24,f54])).

fof(f24,plain,
    ( k1_xboole_0 != sK1
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f338,plain,
    ( ~ r2_hidden(sK0,sK1)
    | r1_tarski(sK2,sK1)
    | sK1 = sK2
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f41,f301])).

fof(f301,plain,
    ( sK0 = sK4(sK2,sK1)
    | sK1 = sK2
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f288,f214])).

fof(f288,plain,
    ( ~ r2_hidden(sK0,sK2)
    | sK1 = sK2
    | sK0 = sK4(sK2,sK1) ),
    inference(duplicate_literal_removal,[],[f283])).

fof(f283,plain,
    ( ~ r2_hidden(sK0,sK2)
    | sK1 = sK2
    | sK0 = sK4(sK2,sK1)
    | sK1 = sK2 ),
    inference(resolution,[],[f281,f221])).

fof(f221,plain,(
    ! [X4] :
      ( ~ r1_tarski(X4,sK2)
      | sK0 = sK4(sK2,X4)
      | sK2 = X4 ) ),
    inference(resolution,[],[f210,f38])).

fof(f281,plain,
    ( r1_tarski(sK1,sK2)
    | ~ r2_hidden(sK0,sK2)
    | sK1 = sK2 ),
    inference(superposition,[],[f41,f279])).

fof(f287,plain,
    ( ~ r1_tarski(sK2,sK1)
    | sK1 = sK2
    | ~ r2_hidden(sK0,sK2) ),
    inference(duplicate_literal_removal,[],[f286])).

fof(f286,plain,
    ( ~ r2_hidden(sK0,sK2)
    | sK1 = sK2
    | ~ r1_tarski(sK2,sK1)
    | sK1 = sK2 ),
    inference(resolution,[],[f281,f38])).

fof(f214,plain,
    ( r2_hidden(sK0,sK2)
    | k1_xboole_0 = sK2 ),
    inference(duplicate_literal_removal,[],[f213])).

fof(f213,plain,
    ( r2_hidden(sK0,sK2)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f28,f208])).

fof(f208,plain,
    ( sK0 = sK3(sK2)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f205,f28])).

fof(f76,plain,
    ( sK1 != sK2
    | sK1 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(inner_rewriting,[],[f56])).

fof(f56,plain,
    ( sK1 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | sK2 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f25,f54,f54])).

fof(f25,plain,
    ( sK1 != k1_tarski(sK0)
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f58,plain,
    ( sK1 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 != sK2 ),
    inference(definition_unfolding,[],[f23,f54])).

fof(f23,plain,
    ( sK1 != k1_tarski(sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f19])).

fof(f629,plain,(
    sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(backward_demodulation,[],[f437,f626])).

fof(f626,plain,(
    sK1 = k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1)) ),
    inference(resolution,[],[f623,f63])).

fof(f623,plain,(
    r1_tarski(k1_xboole_0,sK1) ),
    inference(subsumption_resolution,[],[f621,f500])).

fof(f500,plain,(
    r2_hidden(sK0,sK1) ),
    inference(global_subsumption,[],[f101,f378,f499])).

fof(f499,plain,
    ( k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | r2_hidden(sK0,sK1) ),
    inference(forward_demodulation,[],[f498,f437])).

fof(f498,plain,
    ( k1_xboole_0 = k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1))
    | r2_hidden(sK0,sK1) ),
    inference(forward_demodulation,[],[f495,f60])).

fof(f495,plain,
    ( r2_hidden(sK0,sK1)
    | k1_xboole_0 = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k1_xboole_0)) ),
    inference(resolution,[],[f488,f63])).

fof(f488,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | r2_hidden(sK0,sK1) ),
    inference(superposition,[],[f40,f485])).

fof(f485,plain,(
    sK0 = sK4(sK1,k1_xboole_0) ),
    inference(global_subsumption,[],[f378,f438,f470])).

fof(f470,plain,
    ( sK0 = sK4(sK1,k1_xboole_0)
    | k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f418,f376])).

fof(f418,plain,
    ( k1_xboole_0 = sK1
    | sK0 = sK4(sK1,sK2) ),
    inference(backward_demodulation,[],[f279,f376])).

fof(f438,plain,
    ( sK0 = sK4(sK1,k1_xboole_0)
    | k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(forward_demodulation,[],[f381,f376])).

fof(f381,plain,
    ( k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | sK0 = sK4(sK1,sK2) ),
    inference(backward_demodulation,[],[f129,f376])).

fof(f378,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(backward_demodulation,[],[f57,f376])).

fof(f621,plain,
    ( ~ r2_hidden(sK0,sK1)
    | r1_tarski(k1_xboole_0,sK1) ),
    inference(superposition,[],[f41,f619])).

fof(f619,plain,(
    sK0 = sK4(k1_xboole_0,sK1) ),
    inference(subsumption_resolution,[],[f612,f436])).

fof(f612,plain,
    ( sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | sK0 = sK4(k1_xboole_0,sK1) ),
    inference(superposition,[],[f457,f437])).

fof(f457,plain,(
    ! [X1] :
      ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)) = X1
      | sK0 = sK4(k1_xboole_0,X1) ) ),
    inference(forward_demodulation,[],[f407,f376])).

fof(f407,plain,(
    ! [X1] :
      ( sK0 = sK4(k1_xboole_0,X1)
      | k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,X1)) = X1 ) ),
    inference(backward_demodulation,[],[f219,f376])).

fof(f219,plain,(
    ! [X1] :
      ( sK0 = sK4(sK2,X1)
      | k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,X1)) = X1 ) ),
    inference(resolution,[],[f210,f63])).

fof(f437,plain,(
    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1)) ),
    inference(forward_demodulation,[],[f377,f60])).

fof(f377,plain,(
    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f55,f376])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:35:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.53  % (3590)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (3582)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (3576)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (3568)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (3574)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (3567)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (3572)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (3570)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (3573)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.55  % (3571)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.55  % (3595)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (3592)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (3577)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.48/0.55  % (3577)Refutation not found, incomplete strategy% (3577)------------------------------
% 1.48/0.55  % (3577)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.55  % (3577)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.55  
% 1.48/0.55  % (3577)Memory used [KB]: 10618
% 1.48/0.55  % (3577)Time elapsed: 0.128 s
% 1.48/0.55  % (3577)------------------------------
% 1.48/0.55  % (3577)------------------------------
% 1.48/0.56  % (3580)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.48/0.56  % (3581)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.48/0.56  % (3585)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.48/0.56  % (3575)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.48/0.56  % (3593)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.48/0.57  % (3591)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.48/0.57  % (3569)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.48/0.57  % (3596)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.60/0.57  % (3583)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.60/0.57  % (3586)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.60/0.58  % (3578)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.60/0.58  % (3594)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.60/0.58  % (3588)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.60/0.58  % (3589)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.60/0.58  % (3587)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.60/0.58  % (3584)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.60/0.58  % (3579)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.60/0.59  % (3573)Refutation found. Thanks to Tanya!
% 1.60/0.59  % SZS status Theorem for theBenchmark
% 1.60/0.59  % SZS output start Proof for theBenchmark
% 1.60/0.59  fof(f630,plain,(
% 1.60/0.59    $false),
% 1.60/0.59    inference(subsumption_resolution,[],[f629,f436])).
% 1.60/0.59  fof(f436,plain,(
% 1.60/0.59    sK1 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 1.60/0.59    inference(trivial_inequality_removal,[],[f379])).
% 1.60/0.59  fof(f379,plain,(
% 1.60/0.59    k1_xboole_0 != k1_xboole_0 | sK1 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 1.60/0.59    inference(backward_demodulation,[],[f58,f376])).
% 1.60/0.59  fof(f376,plain,(
% 1.60/0.59    k1_xboole_0 = sK2),
% 1.60/0.59    inference(global_subsumption,[],[f76,f341,f375])).
% 1.60/0.59  fof(f375,plain,(
% 1.60/0.59    sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 = sK2),
% 1.60/0.59    inference(forward_demodulation,[],[f342,f124])).
% 1.60/0.59  fof(f124,plain,(
% 1.60/0.59    ( ! [X0] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X0)) = X0) )),
% 1.60/0.59    inference(resolution,[],[f63,f71])).
% 1.60/0.59  fof(f71,plain,(
% 1.60/0.59    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.60/0.59    inference(equality_resolution,[],[f37])).
% 1.60/0.59  fof(f37,plain,(
% 1.60/0.59    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.60/0.59    inference(cnf_transformation,[],[f4])).
% 1.60/0.59  fof(f4,axiom,(
% 1.60/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.60/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.60/0.59  fof(f63,plain,(
% 1.60/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = X1) )),
% 1.60/0.59    inference(definition_unfolding,[],[f35,f53])).
% 1.60/0.59  fof(f53,plain,(
% 1.60/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 1.60/0.59    inference(definition_unfolding,[],[f32,f52])).
% 1.60/0.59  fof(f52,plain,(
% 1.60/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.60/0.59    inference(definition_unfolding,[],[f31,f51])).
% 1.60/0.59  fof(f51,plain,(
% 1.60/0.59    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.60/0.59    inference(definition_unfolding,[],[f46,f50])).
% 1.60/0.59  fof(f50,plain,(
% 1.60/0.59    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.60/0.59    inference(cnf_transformation,[],[f14])).
% 1.60/0.59  fof(f14,axiom,(
% 1.60/0.59    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.60/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.60/0.59  fof(f46,plain,(
% 1.60/0.59    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.60/0.59    inference(cnf_transformation,[],[f13])).
% 1.60/0.59  fof(f13,axiom,(
% 1.60/0.59    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.60/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.60/0.59  fof(f31,plain,(
% 1.60/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.60/0.59    inference(cnf_transformation,[],[f12])).
% 1.60/0.59  fof(f12,axiom,(
% 1.60/0.59    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.60/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.60/0.59  fof(f32,plain,(
% 1.60/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.60/0.59    inference(cnf_transformation,[],[f15])).
% 1.60/0.59  fof(f15,axiom,(
% 1.60/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.60/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.60/0.59  fof(f35,plain,(
% 1.60/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.60/0.59    inference(cnf_transformation,[],[f21])).
% 1.60/0.59  fof(f21,plain,(
% 1.60/0.59    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.60/0.59    inference(ennf_transformation,[],[f5])).
% 1.60/0.59  fof(f5,axiom,(
% 1.60/0.59    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.60/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.60/0.59  fof(f342,plain,(
% 1.60/0.59    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | k1_xboole_0 = sK2),
% 1.60/0.59    inference(superposition,[],[f55,f341])).
% 1.60/0.59  fof(f55,plain,(
% 1.60/0.59    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2))),
% 1.60/0.59    inference(definition_unfolding,[],[f26,f54,f53])).
% 1.60/0.59  fof(f54,plain,(
% 1.60/0.59    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.60/0.59    inference(definition_unfolding,[],[f27,f52])).
% 1.60/0.59  fof(f27,plain,(
% 1.60/0.59    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.60/0.59    inference(cnf_transformation,[],[f11])).
% 1.60/0.59  fof(f11,axiom,(
% 1.60/0.59    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.60/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.60/0.59  fof(f26,plain,(
% 1.60/0.59    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.60/0.59    inference(cnf_transformation,[],[f19])).
% 1.60/0.59  fof(f19,plain,(
% 1.60/0.59    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.60/0.59    inference(ennf_transformation,[],[f18])).
% 1.60/0.59  fof(f18,negated_conjecture,(
% 1.60/0.59    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.60/0.59    inference(negated_conjecture,[],[f17])).
% 1.60/0.59  fof(f17,conjecture,(
% 1.60/0.59    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.60/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 1.60/0.59  fof(f341,plain,(
% 1.60/0.59    sK1 = sK2 | k1_xboole_0 = sK2),
% 1.60/0.59    inference(global_subsumption,[],[f214,f287,f340])).
% 1.60/0.59  fof(f340,plain,(
% 1.60/0.59    r1_tarski(sK2,sK1) | sK1 = sK2 | k1_xboole_0 = sK2),
% 1.60/0.59    inference(subsumption_resolution,[],[f338,f297])).
% 1.60/0.59  fof(f297,plain,(
% 1.60/0.59    r2_hidden(sK0,sK1) | sK1 = sK2),
% 1.60/0.59    inference(global_subsumption,[],[f57,f101,f296])).
% 1.60/0.59  fof(f296,plain,(
% 1.60/0.59    sK2 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) | r2_hidden(sK0,sK1) | sK1 = sK2),
% 1.60/0.59    inference(forward_demodulation,[],[f291,f55])).
% 1.60/0.59  fof(f291,plain,(
% 1.60/0.59    r2_hidden(sK0,sK1) | sK1 = sK2 | sK2 = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2))),
% 1.60/0.59    inference(resolution,[],[f282,f63])).
% 1.60/0.59  fof(f282,plain,(
% 1.60/0.59    r1_tarski(sK1,sK2) | r2_hidden(sK0,sK1) | sK1 = sK2),
% 1.60/0.59    inference(superposition,[],[f40,f279])).
% 1.60/0.59  fof(f279,plain,(
% 1.60/0.59    sK0 = sK4(sK1,sK2) | sK1 = sK2),
% 1.60/0.59    inference(global_subsumption,[],[f101,f144,f278])).
% 1.60/0.59  fof(f278,plain,(
% 1.60/0.59    ~r2_hidden(sK0,sK1) | sK0 = sK4(sK1,sK2) | sK1 = sK2),
% 1.60/0.59    inference(subsumption_resolution,[],[f276,f104])).
% 1.60/0.59  fof(f104,plain,(
% 1.60/0.59    ( ! [X2] : (~r1_tarski(X2,sK1) | sK0 = sK4(sK1,X2) | sK1 = X2) )),
% 1.60/0.59    inference(resolution,[],[f99,f38])).
% 1.60/0.59  fof(f38,plain,(
% 1.60/0.59    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.60/0.59    inference(cnf_transformation,[],[f4])).
% 1.60/0.59  fof(f99,plain,(
% 1.60/0.59    ( ! [X0] : (r1_tarski(sK1,X0) | sK0 = sK4(sK1,X0)) )),
% 1.60/0.59    inference(resolution,[],[f94,f40])).
% 1.60/0.59  fof(f94,plain,(
% 1.60/0.59    ( ! [X2] : (~r2_hidden(X2,sK1) | sK0 = X2) )),
% 1.60/0.59    inference(resolution,[],[f73,f85])).
% 1.60/0.59  fof(f85,plain,(
% 1.60/0.59    ( ! [X0] : (r2_hidden(X0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(X0,sK1)) )),
% 1.60/0.59    inference(resolution,[],[f84,f39])).
% 1.60/0.59  fof(f39,plain,(
% 1.60/0.59    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.60/0.59    inference(cnf_transformation,[],[f22])).
% 1.60/0.59  fof(f22,plain,(
% 1.60/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.60/0.59    inference(ennf_transformation,[],[f2])).
% 1.60/0.59  fof(f2,axiom,(
% 1.60/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.60/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.60/0.59  fof(f84,plain,(
% 1.60/0.59    r1_tarski(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 1.60/0.59    inference(superposition,[],[f59,f55])).
% 1.60/0.59  fof(f59,plain,(
% 1.60/0.59    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 1.60/0.59    inference(definition_unfolding,[],[f29,f53])).
% 1.60/0.59  fof(f29,plain,(
% 1.60/0.59    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.60/0.59    inference(cnf_transformation,[],[f8])).
% 1.60/0.59  fof(f8,axiom,(
% 1.60/0.59    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.60/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.60/0.59  fof(f73,plain,(
% 1.60/0.59    ( ! [X2,X0] : (~r2_hidden(X2,k3_enumset1(X0,X0,X0,X0,X0)) | X0 = X2) )),
% 1.60/0.59    inference(equality_resolution,[],[f66])).
% 1.60/0.59  fof(f66,plain,(
% 1.60/0.59    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 1.60/0.59    inference(definition_unfolding,[],[f43,f54])).
% 1.60/0.59  fof(f43,plain,(
% 1.60/0.59    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 1.60/0.59    inference(cnf_transformation,[],[f10])).
% 1.60/0.59  fof(f10,axiom,(
% 1.60/0.59    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.60/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.60/0.59  fof(f276,plain,(
% 1.60/0.59    ~r2_hidden(sK0,sK1) | r1_tarski(sK2,sK1) | sK0 = sK4(sK1,sK2) | sK1 = sK2),
% 1.60/0.59    inference(superposition,[],[f41,f222])).
% 1.60/0.59  fof(f222,plain,(
% 1.60/0.59    sK0 = sK4(sK2,sK1) | sK0 = sK4(sK1,sK2) | sK1 = sK2),
% 1.60/0.59    inference(resolution,[],[f210,f104])).
% 1.60/0.59  fof(f210,plain,(
% 1.60/0.59    ( ! [X0] : (r1_tarski(sK2,X0) | sK0 = sK4(sK2,X0)) )),
% 1.60/0.59    inference(resolution,[],[f205,f40])).
% 1.60/0.59  fof(f205,plain,(
% 1.60/0.59    ( ! [X1] : (~r2_hidden(X1,sK2) | sK0 = X1) )),
% 1.60/0.59    inference(resolution,[],[f201,f73])).
% 1.60/0.59  fof(f201,plain,(
% 1.60/0.59    ( ! [X0] : (r2_hidden(X0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(X0,sK2)) )),
% 1.60/0.59    inference(resolution,[],[f196,f39])).
% 1.60/0.59  fof(f196,plain,(
% 1.60/0.59    r1_tarski(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 1.60/0.59    inference(superposition,[],[f151,f55])).
% 1.60/0.59  fof(f151,plain,(
% 1.60/0.59    ( ! [X4,X5] : (r1_tarski(X4,k3_tarski(k3_enumset1(X5,X5,X5,X5,X4)))) )),
% 1.60/0.59    inference(superposition,[],[f59,f60])).
% 1.60/0.59  fof(f60,plain,(
% 1.60/0.59    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)) )),
% 1.60/0.59    inference(definition_unfolding,[],[f30,f52,f52])).
% 1.60/0.59  fof(f30,plain,(
% 1.60/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.60/0.59    inference(cnf_transformation,[],[f9])).
% 1.60/0.59  fof(f9,axiom,(
% 1.60/0.59    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.60/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.60/0.59  fof(f41,plain,(
% 1.60/0.59    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.60/0.59    inference(cnf_transformation,[],[f22])).
% 1.60/0.59  fof(f144,plain,(
% 1.60/0.59    k1_xboole_0 != sK1 | sK0 = sK4(sK1,sK2)),
% 1.60/0.59    inference(trivial_inequality_removal,[],[f135])).
% 1.60/0.59  fof(f135,plain,(
% 1.60/0.59    sK2 != sK2 | k1_xboole_0 != sK1 | sK0 = sK4(sK1,sK2)),
% 1.60/0.59    inference(superposition,[],[f57,f129])).
% 1.60/0.59  fof(f129,plain,(
% 1.60/0.59    sK2 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) | sK0 = sK4(sK1,sK2)),
% 1.60/0.59    inference(superposition,[],[f127,f55])).
% 1.60/0.59  fof(f127,plain,(
% 1.60/0.59    ( ! [X3] : (k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,X3)) = X3 | sK0 = sK4(sK1,X3)) )),
% 1.60/0.59    inference(resolution,[],[f63,f99])).
% 1.60/0.59  fof(f40,plain,(
% 1.60/0.59    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.60/0.59    inference(cnf_transformation,[],[f22])).
% 1.60/0.59  fof(f101,plain,(
% 1.60/0.59    r2_hidden(sK0,sK1) | k1_xboole_0 = sK1),
% 1.60/0.59    inference(duplicate_literal_removal,[],[f100])).
% 1.60/0.59  fof(f100,plain,(
% 1.60/0.59    r2_hidden(sK0,sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = sK1),
% 1.60/0.59    inference(superposition,[],[f28,f98])).
% 1.60/0.59  fof(f98,plain,(
% 1.60/0.59    sK0 = sK3(sK1) | k1_xboole_0 = sK1),
% 1.60/0.59    inference(resolution,[],[f94,f28])).
% 1.60/0.59  fof(f28,plain,(
% 1.60/0.59    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 1.60/0.59    inference(cnf_transformation,[],[f20])).
% 1.60/0.59  fof(f20,plain,(
% 1.60/0.59    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.60/0.59    inference(ennf_transformation,[],[f3])).
% 1.60/0.59  fof(f3,axiom,(
% 1.60/0.59    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.60/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.60/0.59  fof(f57,plain,(
% 1.60/0.59    sK2 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 != sK1),
% 1.60/0.59    inference(definition_unfolding,[],[f24,f54])).
% 1.60/0.59  fof(f24,plain,(
% 1.60/0.59    k1_xboole_0 != sK1 | sK2 != k1_tarski(sK0)),
% 1.60/0.59    inference(cnf_transformation,[],[f19])).
% 1.60/0.59  fof(f338,plain,(
% 1.60/0.59    ~r2_hidden(sK0,sK1) | r1_tarski(sK2,sK1) | sK1 = sK2 | k1_xboole_0 = sK2),
% 1.60/0.59    inference(superposition,[],[f41,f301])).
% 1.60/0.59  fof(f301,plain,(
% 1.60/0.59    sK0 = sK4(sK2,sK1) | sK1 = sK2 | k1_xboole_0 = sK2),
% 1.60/0.59    inference(resolution,[],[f288,f214])).
% 1.60/0.59  fof(f288,plain,(
% 1.60/0.59    ~r2_hidden(sK0,sK2) | sK1 = sK2 | sK0 = sK4(sK2,sK1)),
% 1.60/0.59    inference(duplicate_literal_removal,[],[f283])).
% 1.60/0.59  fof(f283,plain,(
% 1.60/0.59    ~r2_hidden(sK0,sK2) | sK1 = sK2 | sK0 = sK4(sK2,sK1) | sK1 = sK2),
% 1.60/0.59    inference(resolution,[],[f281,f221])).
% 1.60/0.59  fof(f221,plain,(
% 1.60/0.59    ( ! [X4] : (~r1_tarski(X4,sK2) | sK0 = sK4(sK2,X4) | sK2 = X4) )),
% 1.60/0.59    inference(resolution,[],[f210,f38])).
% 1.60/0.59  fof(f281,plain,(
% 1.60/0.59    r1_tarski(sK1,sK2) | ~r2_hidden(sK0,sK2) | sK1 = sK2),
% 1.60/0.59    inference(superposition,[],[f41,f279])).
% 1.60/0.59  fof(f287,plain,(
% 1.60/0.59    ~r1_tarski(sK2,sK1) | sK1 = sK2 | ~r2_hidden(sK0,sK2)),
% 1.60/0.59    inference(duplicate_literal_removal,[],[f286])).
% 1.60/0.59  fof(f286,plain,(
% 1.60/0.59    ~r2_hidden(sK0,sK2) | sK1 = sK2 | ~r1_tarski(sK2,sK1) | sK1 = sK2),
% 1.60/0.59    inference(resolution,[],[f281,f38])).
% 1.60/0.59  fof(f214,plain,(
% 1.60/0.59    r2_hidden(sK0,sK2) | k1_xboole_0 = sK2),
% 1.60/0.59    inference(duplicate_literal_removal,[],[f213])).
% 1.60/0.59  fof(f213,plain,(
% 1.60/0.59    r2_hidden(sK0,sK2) | k1_xboole_0 = sK2 | k1_xboole_0 = sK2),
% 1.60/0.59    inference(superposition,[],[f28,f208])).
% 1.60/0.59  fof(f208,plain,(
% 1.60/0.59    sK0 = sK3(sK2) | k1_xboole_0 = sK2),
% 1.60/0.59    inference(resolution,[],[f205,f28])).
% 1.60/0.59  fof(f76,plain,(
% 1.60/0.59    sK1 != sK2 | sK1 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 1.60/0.59    inference(inner_rewriting,[],[f56])).
% 1.60/0.59  fof(f56,plain,(
% 1.60/0.59    sK1 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) | sK2 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 1.60/0.59    inference(definition_unfolding,[],[f25,f54,f54])).
% 1.60/0.59  fof(f25,plain,(
% 1.60/0.59    sK1 != k1_tarski(sK0) | sK2 != k1_tarski(sK0)),
% 1.60/0.59    inference(cnf_transformation,[],[f19])).
% 1.60/0.59  fof(f58,plain,(
% 1.60/0.59    sK1 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 != sK2),
% 1.60/0.59    inference(definition_unfolding,[],[f23,f54])).
% 1.60/0.59  fof(f23,plain,(
% 1.60/0.59    sK1 != k1_tarski(sK0) | k1_xboole_0 != sK2),
% 1.60/0.59    inference(cnf_transformation,[],[f19])).
% 1.60/0.59  fof(f629,plain,(
% 1.60/0.59    sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 1.60/0.59    inference(backward_demodulation,[],[f437,f626])).
% 1.60/0.59  fof(f626,plain,(
% 1.60/0.59    sK1 = k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1))),
% 1.60/0.59    inference(resolution,[],[f623,f63])).
% 1.60/0.59  fof(f623,plain,(
% 1.60/0.59    r1_tarski(k1_xboole_0,sK1)),
% 1.60/0.59    inference(subsumption_resolution,[],[f621,f500])).
% 1.60/0.59  fof(f500,plain,(
% 1.60/0.59    r2_hidden(sK0,sK1)),
% 1.60/0.59    inference(global_subsumption,[],[f101,f378,f499])).
% 1.60/0.59  fof(f499,plain,(
% 1.60/0.59    k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) | r2_hidden(sK0,sK1)),
% 1.60/0.59    inference(forward_demodulation,[],[f498,f437])).
% 1.60/0.59  fof(f498,plain,(
% 1.60/0.59    k1_xboole_0 = k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1)) | r2_hidden(sK0,sK1)),
% 1.60/0.59    inference(forward_demodulation,[],[f495,f60])).
% 1.60/0.59  fof(f495,plain,(
% 1.60/0.59    r2_hidden(sK0,sK1) | k1_xboole_0 = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k1_xboole_0))),
% 1.60/0.59    inference(resolution,[],[f488,f63])).
% 1.60/0.59  fof(f488,plain,(
% 1.60/0.59    r1_tarski(sK1,k1_xboole_0) | r2_hidden(sK0,sK1)),
% 1.60/0.59    inference(superposition,[],[f40,f485])).
% 1.60/0.59  fof(f485,plain,(
% 1.60/0.59    sK0 = sK4(sK1,k1_xboole_0)),
% 1.60/0.59    inference(global_subsumption,[],[f378,f438,f470])).
% 1.60/0.59  fof(f470,plain,(
% 1.60/0.59    sK0 = sK4(sK1,k1_xboole_0) | k1_xboole_0 = sK1),
% 1.60/0.59    inference(forward_demodulation,[],[f418,f376])).
% 1.60/0.59  fof(f418,plain,(
% 1.60/0.59    k1_xboole_0 = sK1 | sK0 = sK4(sK1,sK2)),
% 1.60/0.59    inference(backward_demodulation,[],[f279,f376])).
% 1.60/0.59  fof(f438,plain,(
% 1.60/0.59    sK0 = sK4(sK1,k1_xboole_0) | k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 1.60/0.59    inference(forward_demodulation,[],[f381,f376])).
% 1.60/0.59  fof(f381,plain,(
% 1.60/0.59    k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) | sK0 = sK4(sK1,sK2)),
% 1.60/0.59    inference(backward_demodulation,[],[f129,f376])).
% 1.60/0.59  fof(f378,plain,(
% 1.60/0.59    k1_xboole_0 != sK1 | k1_xboole_0 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 1.60/0.59    inference(backward_demodulation,[],[f57,f376])).
% 1.60/0.59  fof(f621,plain,(
% 1.60/0.59    ~r2_hidden(sK0,sK1) | r1_tarski(k1_xboole_0,sK1)),
% 1.60/0.59    inference(superposition,[],[f41,f619])).
% 1.60/0.59  fof(f619,plain,(
% 1.60/0.59    sK0 = sK4(k1_xboole_0,sK1)),
% 1.60/0.59    inference(subsumption_resolution,[],[f612,f436])).
% 1.60/0.59  fof(f612,plain,(
% 1.60/0.59    sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) | sK0 = sK4(k1_xboole_0,sK1)),
% 1.60/0.59    inference(superposition,[],[f457,f437])).
% 1.60/0.59  fof(f457,plain,(
% 1.60/0.59    ( ! [X1] : (k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)) = X1 | sK0 = sK4(k1_xboole_0,X1)) )),
% 1.60/0.59    inference(forward_demodulation,[],[f407,f376])).
% 1.60/0.59  fof(f407,plain,(
% 1.60/0.59    ( ! [X1] : (sK0 = sK4(k1_xboole_0,X1) | k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,X1)) = X1) )),
% 1.60/0.59    inference(backward_demodulation,[],[f219,f376])).
% 1.60/0.59  fof(f219,plain,(
% 1.60/0.59    ( ! [X1] : (sK0 = sK4(sK2,X1) | k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,X1)) = X1) )),
% 1.60/0.59    inference(resolution,[],[f210,f63])).
% 1.60/0.59  fof(f437,plain,(
% 1.60/0.59    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1))),
% 1.60/0.59    inference(forward_demodulation,[],[f377,f60])).
% 1.60/0.59  fof(f377,plain,(
% 1.60/0.59    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,k1_xboole_0))),
% 1.60/0.59    inference(backward_demodulation,[],[f55,f376])).
% 1.60/0.59  % SZS output end Proof for theBenchmark
% 1.60/0.59  % (3573)------------------------------
% 1.60/0.59  % (3573)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.59  % (3573)Termination reason: Refutation
% 1.60/0.59  
% 1.60/0.59  % (3573)Memory used [KB]: 6652
% 1.60/0.59  % (3573)Time elapsed: 0.173 s
% 1.60/0.59  % (3573)------------------------------
% 1.60/0.59  % (3573)------------------------------
% 1.60/0.60  % (3566)Success in time 0.23 s
%------------------------------------------------------------------------------
