%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:21 EST 2020

% Result     : Theorem 2.07s
% Output     : Refutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 374 expanded)
%              Number of leaves         :   12 ( 113 expanded)
%              Depth                    :   22
%              Number of atoms          :  170 ( 613 expanded)
%              Number of equality atoms :   85 ( 431 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f814,plain,(
    $false ),
    inference(subsumption_resolution,[],[f813,f80])).

fof(f80,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f49,f50])).

fof(f50,plain,(
    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(definition_unfolding,[],[f19,f24,f48])).

fof(f48,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f22,f47])).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f23,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f26,f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f39,f44])).

fof(f44,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f40,f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f41,f42])).

fof(f42,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f41,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f39,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f26,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f23,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f22,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f19,plain,(
    k3_xboole_0(sK1,sK2) = k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_tarski(X3) != k3_xboole_0(X0,X2)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_tarski(X3) != k3_xboole_0(X0,X2)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r2_hidden(X3,X0)
          & k3_xboole_0(X1,X2) = k1_tarski(X3)
          & r1_tarski(X0,X1) )
       => k1_tarski(X3) = k3_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
     => k1_tarski(X3) = k3_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_zfmisc_1)).

fof(f49,plain,(
    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(definition_unfolding,[],[f21,f48,f24])).

fof(f21,plain,(
    k1_tarski(sK3) != k3_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f813,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f812,f20])).

fof(f20,plain,(
    r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f812,plain,
    ( ~ r2_hidden(sK3,sK0)
    | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f811,f84])).

fof(f84,plain,(
    r2_hidden(sK3,sK2) ),
    inference(resolution,[],[f81,f69])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f37,f24])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f81,plain,(
    r2_hidden(sK3,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(superposition,[],[f66,f50])).

fof(f66,plain,(
    ! [X3,X1] : r2_hidden(X3,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X1)) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,X2)
      | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X1) != X2 ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X3
      | r2_hidden(X3,X2)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f31,f47])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X3
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f811,plain,
    ( ~ r2_hidden(sK3,sK2)
    | ~ r2_hidden(sK3,sK0)
    | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f806,f81])).

fof(f806,plain,
    ( ~ r2_hidden(sK3,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | ~ r2_hidden(sK3,sK2)
    | ~ r2_hidden(sK3,sK0)
    | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f62,f801])).

fof(f801,plain,(
    sK3 = sK5(sK0,sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(subsumption_resolution,[],[f798,f80])).

fof(f798,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
    | sK3 = sK5(sK0,sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(duplicate_literal_removal,[],[f783])).

fof(f783,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
    | sK3 = sK5(sK0,sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | sK3 = sK5(sK0,sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(resolution,[],[f672,f97])).

fof(f97,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
      | sK3 = X0 ) ),
    inference(duplicate_literal_removal,[],[f96])).

fof(f96,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
      | sK3 = X0
      | sK3 = X0 ) ),
    inference(superposition,[],[f67,f50])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))
      | X1 = X3
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f30,f47])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f672,plain,(
    ! [X2] :
      ( r2_hidden(sK5(sK0,sK2,X2),X2)
      | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = X2
      | sK3 = sK5(sK0,sK2,X2) ) ),
    inference(duplicate_literal_removal,[],[f666])).

fof(f666,plain,(
    ! [X2] :
      ( r2_hidden(sK5(sK0,sK2,X2),X2)
      | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = X2
      | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = X2
      | sK3 = sK5(sK0,sK2,X2)
      | r2_hidden(sK5(sK0,sK2,X2),X2) ) ),
    inference(resolution,[],[f586,f109])).

fof(f109,plain,(
    ! [X19,X18] :
      ( ~ r2_hidden(sK5(X18,sK2,X19),sK1)
      | k4_xboole_0(X18,k4_xboole_0(X18,sK2)) = X19
      | sK3 = sK5(X18,sK2,X19)
      | r2_hidden(sK5(X18,sK2,X19),X19) ) ),
    inference(resolution,[],[f60,f100])).

fof(f100,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | sK3 = X0
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f97,f68])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f38,f24])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X1)
      | r2_hidden(sK5(X0,X1,X2),X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f35,f24])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X1)
      | r2_hidden(sK5(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f586,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(sK0,X0,X1),X1)
      | r2_hidden(sK5(sK0,X0,X1),sK1)
      | k4_xboole_0(sK0,k4_xboole_0(sK0,X0)) = X1 ) ),
    inference(resolution,[],[f126,f18])).

fof(f18,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f126,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X0,X3)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | r2_hidden(sK5(X0,X1,X2),X2)
      | r2_hidden(sK5(X0,X1,X2),X3) ) ),
    inference(resolution,[],[f61,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X0)
      | r2_hidden(sK5(X0,X1,X2),X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f34,f24])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X0)
      | r2_hidden(sK5(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1,X2),X2)
      | ~ r2_hidden(sK5(X0,X1,X2),X1)
      | ~ r2_hidden(sK5(X0,X1,X2),X0)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f33,f24])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1,X2),X0)
      | ~ r2_hidden(sK5(X0,X1,X2),X1)
      | ~ r2_hidden(sK5(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:16:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (12519)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (12540)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.51  % (12528)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.51  % (12541)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.51  % (12533)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.51  % (12520)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (12525)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.52  % (12534)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.52  % (12521)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (12532)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (12536)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.53  % (12531)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.53  % (12537)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.53  % (12542)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.53  % (12518)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (12529)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (12517)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (12546)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (12523)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (12524)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (12530)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (12545)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (12538)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  % (12526)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.55  % (12544)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.55  % (12543)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.55  % (12535)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  % (12527)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.56  % (12539)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.56  % (12547)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 2.07/0.63  % (12524)Refutation found. Thanks to Tanya!
% 2.07/0.63  % SZS status Theorem for theBenchmark
% 2.07/0.63  % SZS output start Proof for theBenchmark
% 2.07/0.63  fof(f814,plain,(
% 2.07/0.63    $false),
% 2.07/0.63    inference(subsumption_resolution,[],[f813,f80])).
% 2.07/0.63  fof(f80,plain,(
% 2.07/0.63    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 2.07/0.63    inference(superposition,[],[f49,f50])).
% 2.07/0.63  fof(f50,plain,(
% 2.07/0.63    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 2.07/0.63    inference(definition_unfolding,[],[f19,f24,f48])).
% 2.07/0.63  fof(f48,plain,(
% 2.07/0.63    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.07/0.63    inference(definition_unfolding,[],[f22,f47])).
% 2.07/0.63  fof(f47,plain,(
% 2.07/0.63    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.07/0.63    inference(definition_unfolding,[],[f23,f46])).
% 2.07/0.63  fof(f46,plain,(
% 2.07/0.63    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.07/0.63    inference(definition_unfolding,[],[f26,f45])).
% 2.07/0.63  fof(f45,plain,(
% 2.07/0.63    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.07/0.63    inference(definition_unfolding,[],[f39,f44])).
% 2.07/0.63  fof(f44,plain,(
% 2.07/0.63    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.07/0.63    inference(definition_unfolding,[],[f40,f43])).
% 2.07/0.63  fof(f43,plain,(
% 2.07/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.07/0.63    inference(definition_unfolding,[],[f41,f42])).
% 2.07/0.63  fof(f42,plain,(
% 2.07/0.63    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 2.07/0.63    inference(cnf_transformation,[],[f11])).
% 2.07/0.63  fof(f11,axiom,(
% 2.07/0.63    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 2.07/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 2.07/0.63  fof(f41,plain,(
% 2.07/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 2.07/0.63    inference(cnf_transformation,[],[f10])).
% 2.07/0.63  fof(f10,axiom,(
% 2.07/0.63    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 2.07/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 2.07/0.63  fof(f40,plain,(
% 2.07/0.63    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.07/0.63    inference(cnf_transformation,[],[f9])).
% 2.07/0.63  fof(f9,axiom,(
% 2.07/0.63    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.07/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 2.07/0.63  fof(f39,plain,(
% 2.07/0.63    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.07/0.63    inference(cnf_transformation,[],[f8])).
% 2.07/0.63  fof(f8,axiom,(
% 2.07/0.63    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 2.07/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 2.07/0.63  fof(f26,plain,(
% 2.07/0.63    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.07/0.63    inference(cnf_transformation,[],[f7])).
% 2.07/0.63  fof(f7,axiom,(
% 2.07/0.63    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.07/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 2.07/0.63  fof(f23,plain,(
% 2.07/0.63    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.07/0.63    inference(cnf_transformation,[],[f6])).
% 2.07/0.63  fof(f6,axiom,(
% 2.07/0.63    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.07/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 2.07/0.63  fof(f22,plain,(
% 2.07/0.63    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.07/0.63    inference(cnf_transformation,[],[f5])).
% 2.07/0.63  fof(f5,axiom,(
% 2.07/0.63    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.07/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 2.07/0.63  fof(f24,plain,(
% 2.07/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.07/0.63    inference(cnf_transformation,[],[f3])).
% 2.07/0.63  fof(f3,axiom,(
% 2.07/0.63    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.07/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.07/0.63  fof(f19,plain,(
% 2.07/0.63    k3_xboole_0(sK1,sK2) = k1_tarski(sK3)),
% 2.07/0.63    inference(cnf_transformation,[],[f16])).
% 2.07/0.63  fof(f16,plain,(
% 2.07/0.63    ? [X0,X1,X2,X3] : (k1_tarski(X3) != k3_xboole_0(X0,X2) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1))),
% 2.07/0.63    inference(flattening,[],[f15])).
% 2.07/0.63  fof(f15,plain,(
% 2.07/0.63    ? [X0,X1,X2,X3] : (k1_tarski(X3) != k3_xboole_0(X0,X2) & (r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)))),
% 2.07/0.63    inference(ennf_transformation,[],[f13])).
% 2.07/0.63  fof(f13,negated_conjecture,(
% 2.07/0.63    ~! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k1_tarski(X3) = k3_xboole_0(X0,X2))),
% 2.07/0.63    inference(negated_conjecture,[],[f12])).
% 2.07/0.63  fof(f12,conjecture,(
% 2.07/0.63    ! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k1_tarski(X3) = k3_xboole_0(X0,X2))),
% 2.07/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_zfmisc_1)).
% 2.07/0.63  fof(f49,plain,(
% 2.07/0.63    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 2.07/0.63    inference(definition_unfolding,[],[f21,f48,f24])).
% 2.07/0.63  fof(f21,plain,(
% 2.07/0.63    k1_tarski(sK3) != k3_xboole_0(sK0,sK2)),
% 2.07/0.63    inference(cnf_transformation,[],[f16])).
% 2.07/0.63  fof(f813,plain,(
% 2.07/0.63    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 2.07/0.63    inference(subsumption_resolution,[],[f812,f20])).
% 2.07/0.63  fof(f20,plain,(
% 2.07/0.63    r2_hidden(sK3,sK0)),
% 2.07/0.63    inference(cnf_transformation,[],[f16])).
% 2.07/0.63  fof(f812,plain,(
% 2.07/0.63    ~r2_hidden(sK3,sK0) | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 2.07/0.63    inference(subsumption_resolution,[],[f811,f84])).
% 2.07/0.63  fof(f84,plain,(
% 2.07/0.63    r2_hidden(sK3,sK2)),
% 2.07/0.63    inference(resolution,[],[f81,f69])).
% 2.07/0.63  fof(f69,plain,(
% 2.07/0.63    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r2_hidden(X3,X1)) )),
% 2.07/0.63    inference(equality_resolution,[],[f58])).
% 2.07/0.63  fof(f58,plain,(
% 2.07/0.63    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 2.07/0.63    inference(definition_unfolding,[],[f37,f24])).
% 2.07/0.63  fof(f37,plain,(
% 2.07/0.63    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 2.07/0.63    inference(cnf_transformation,[],[f2])).
% 2.07/0.63  fof(f2,axiom,(
% 2.07/0.63    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.07/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 2.07/0.63  fof(f81,plain,(
% 2.07/0.63    r2_hidden(sK3,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 2.07/0.63    inference(superposition,[],[f66,f50])).
% 2.07/0.63  fof(f66,plain,(
% 2.07/0.63    ( ! [X3,X1] : (r2_hidden(X3,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X1))) )),
% 2.07/0.63    inference(equality_resolution,[],[f65])).
% 2.07/0.63  fof(f65,plain,(
% 2.07/0.63    ( ! [X2,X3,X1] : (r2_hidden(X3,X2) | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X1) != X2) )),
% 2.07/0.63    inference(equality_resolution,[],[f52])).
% 2.07/0.63  fof(f52,plain,(
% 2.07/0.63    ( ! [X2,X0,X3,X1] : (X0 != X3 | r2_hidden(X3,X2) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2) )),
% 2.07/0.63    inference(definition_unfolding,[],[f31,f47])).
% 2.07/0.63  fof(f31,plain,(
% 2.07/0.63    ( ! [X2,X0,X3,X1] : (X0 != X3 | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 2.07/0.63    inference(cnf_transformation,[],[f4])).
% 2.07/0.63  fof(f4,axiom,(
% 2.07/0.63    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 2.07/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 2.07/0.63  fof(f811,plain,(
% 2.07/0.63    ~r2_hidden(sK3,sK2) | ~r2_hidden(sK3,sK0) | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 2.07/0.63    inference(subsumption_resolution,[],[f806,f81])).
% 2.07/0.63  fof(f806,plain,(
% 2.07/0.63    ~r2_hidden(sK3,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) | ~r2_hidden(sK3,sK2) | ~r2_hidden(sK3,sK0) | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 2.07/0.63    inference(superposition,[],[f62,f801])).
% 2.07/0.63  fof(f801,plain,(
% 2.07/0.63    sK3 = sK5(sK0,sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 2.07/0.63    inference(subsumption_resolution,[],[f798,f80])).
% 2.07/0.63  fof(f798,plain,(
% 2.07/0.63    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) | sK3 = sK5(sK0,sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 2.07/0.63    inference(duplicate_literal_removal,[],[f783])).
% 2.07/0.63  fof(f783,plain,(
% 2.07/0.63    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) | sK3 = sK5(sK0,sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) | sK3 = sK5(sK0,sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 2.07/0.63    inference(resolution,[],[f672,f97])).
% 2.07/0.63  fof(f97,plain,(
% 2.07/0.63    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) | sK3 = X0) )),
% 2.07/0.63    inference(duplicate_literal_removal,[],[f96])).
% 2.07/0.63  fof(f96,plain,(
% 2.07/0.63    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) | sK3 = X0 | sK3 = X0) )),
% 2.07/0.63    inference(superposition,[],[f67,f50])).
% 2.07/0.63  fof(f67,plain,(
% 2.07/0.63    ( ! [X0,X3,X1] : (~r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) | X1 = X3 | X0 = X3) )),
% 2.07/0.63    inference(equality_resolution,[],[f53])).
% 2.07/0.63  fof(f53,plain,(
% 2.07/0.63    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2) )),
% 2.07/0.63    inference(definition_unfolding,[],[f30,f47])).
% 2.07/0.63  fof(f30,plain,(
% 2.07/0.63    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 2.07/0.63    inference(cnf_transformation,[],[f4])).
% 2.07/0.63  fof(f672,plain,(
% 2.07/0.63    ( ! [X2] : (r2_hidden(sK5(sK0,sK2,X2),X2) | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = X2 | sK3 = sK5(sK0,sK2,X2)) )),
% 2.07/0.63    inference(duplicate_literal_removal,[],[f666])).
% 2.07/0.63  fof(f666,plain,(
% 2.07/0.63    ( ! [X2] : (r2_hidden(sK5(sK0,sK2,X2),X2) | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = X2 | k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = X2 | sK3 = sK5(sK0,sK2,X2) | r2_hidden(sK5(sK0,sK2,X2),X2)) )),
% 2.07/0.63    inference(resolution,[],[f586,f109])).
% 2.07/0.63  fof(f109,plain,(
% 2.07/0.63    ( ! [X19,X18] : (~r2_hidden(sK5(X18,sK2,X19),sK1) | k4_xboole_0(X18,k4_xboole_0(X18,sK2)) = X19 | sK3 = sK5(X18,sK2,X19) | r2_hidden(sK5(X18,sK2,X19),X19)) )),
% 2.07/0.63    inference(resolution,[],[f60,f100])).
% 2.07/0.63  fof(f100,plain,(
% 2.07/0.63    ( ! [X0] : (~r2_hidden(X0,sK2) | sK3 = X0 | ~r2_hidden(X0,sK1)) )),
% 2.07/0.63    inference(resolution,[],[f97,f68])).
% 2.07/0.63  fof(f68,plain,(
% 2.07/0.63    ( ! [X0,X3,X1] : (r2_hidden(X3,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) )),
% 2.07/0.63    inference(equality_resolution,[],[f57])).
% 2.07/0.63  fof(f57,plain,(
% 2.07/0.63    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | r2_hidden(X3,X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 2.07/0.63    inference(definition_unfolding,[],[f38,f24])).
% 2.07/0.63  fof(f38,plain,(
% 2.07/0.63    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 2.07/0.63    inference(cnf_transformation,[],[f2])).
% 2.07/0.63  fof(f60,plain,(
% 2.07/0.63    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),X1) | r2_hidden(sK5(X0,X1,X2),X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2) )),
% 2.07/0.63    inference(definition_unfolding,[],[f35,f24])).
% 2.07/0.63  fof(f35,plain,(
% 2.07/0.63    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),X1) | r2_hidden(sK5(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 2.07/0.63    inference(cnf_transformation,[],[f2])).
% 2.07/0.63  fof(f586,plain,(
% 2.07/0.63    ( ! [X0,X1] : (r2_hidden(sK5(sK0,X0,X1),X1) | r2_hidden(sK5(sK0,X0,X1),sK1) | k4_xboole_0(sK0,k4_xboole_0(sK0,X0)) = X1) )),
% 2.07/0.63    inference(resolution,[],[f126,f18])).
% 2.07/0.63  fof(f18,plain,(
% 2.07/0.63    r1_tarski(sK0,sK1)),
% 2.07/0.63    inference(cnf_transformation,[],[f16])).
% 2.07/0.63  fof(f126,plain,(
% 2.07/0.63    ( ! [X2,X0,X3,X1] : (~r1_tarski(X0,X3) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | r2_hidden(sK5(X0,X1,X2),X2) | r2_hidden(sK5(X0,X1,X2),X3)) )),
% 2.07/0.63    inference(resolution,[],[f61,f25])).
% 2.07/0.63  fof(f25,plain,(
% 2.07/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r1_tarski(X0,X1) | r2_hidden(X2,X1)) )),
% 2.07/0.63    inference(cnf_transformation,[],[f17])).
% 2.07/0.63  fof(f17,plain,(
% 2.07/0.63    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 2.07/0.63    inference(ennf_transformation,[],[f14])).
% 2.07/0.63  fof(f14,plain,(
% 2.07/0.63    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.07/0.63    inference(unused_predicate_definition_removal,[],[f1])).
% 2.07/0.63  fof(f1,axiom,(
% 2.07/0.63    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.07/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 2.07/0.63  fof(f61,plain,(
% 2.07/0.63    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2) )),
% 2.07/0.63    inference(definition_unfolding,[],[f34,f24])).
% 2.07/0.63  fof(f34,plain,(
% 2.07/0.63    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 2.07/0.63    inference(cnf_transformation,[],[f2])).
% 2.07/0.63  fof(f62,plain,(
% 2.07/0.63    ( ! [X2,X0,X1] : (~r2_hidden(sK5(X0,X1,X2),X2) | ~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2) )),
% 2.07/0.63    inference(definition_unfolding,[],[f33,f24])).
% 2.07/0.63  fof(f33,plain,(
% 2.07/0.63    ( ! [X2,X0,X1] : (~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 2.07/0.63    inference(cnf_transformation,[],[f2])).
% 2.07/0.63  % SZS output end Proof for theBenchmark
% 2.07/0.63  % (12524)------------------------------
% 2.07/0.63  % (12524)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.07/0.63  % (12524)Termination reason: Refutation
% 2.07/0.63  
% 2.07/0.63  % (12524)Memory used [KB]: 7036
% 2.07/0.63  % (12524)Time elapsed: 0.229 s
% 2.07/0.63  % (12524)------------------------------
% 2.07/0.63  % (12524)------------------------------
% 2.07/0.64  % (12514)Success in time 0.274 s
%------------------------------------------------------------------------------
