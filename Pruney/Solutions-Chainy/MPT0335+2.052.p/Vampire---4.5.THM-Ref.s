%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:22 EST 2020

% Result     : Theorem 2.33s
% Output     : Refutation 2.90s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 287 expanded)
%              Number of leaves         :   12 (  85 expanded)
%              Depth                    :   16
%              Number of atoms          :  162 ( 535 expanded)
%              Number of equality atoms :   73 ( 309 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1343,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1331,f66])).

fof(f66,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f47,f48])).

fof(f48,plain,(
    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(definition_unfolding,[],[f21,f26,f46])).

fof(f46,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f24,f45])).

fof(f45,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f25,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f28,f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f37,f42])).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f38,f41])).

fof(f41,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f40,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f39,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f37,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f28,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f25,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f24,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f21,plain,(
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

fof(f47,plain,(
    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(definition_unfolding,[],[f23,f46,f26])).

fof(f23,plain,(
    k1_tarski(sK3) != k3_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f1331,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f1229,f1230])).

fof(f1230,plain,(
    r2_hidden(sK4(sK0,sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),sK0) ),
    inference(subsumption_resolution,[],[f1216,f66])).

fof(f1216,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
    | r2_hidden(sK4(sK0,sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),sK0) ),
    inference(resolution,[],[f1206,f425])).

fof(f425,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
      | r2_hidden(X2,sK0) ) ),
    inference(superposition,[],[f59,f379])).

fof(f379,plain,(
    k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK0)) ),
    inference(forward_demodulation,[],[f361,f48])).

fof(f361,plain,(
    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k4_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k4_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK0)) ),
    inference(resolution,[],[f57,f22])).

fof(f22,plain,(
    r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f57,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X2,X1)
      | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = k4_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k4_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),X1)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | X0 != X2
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1)) ) ),
    inference(definition_unfolding,[],[f30,f46,f26,f45])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | X0 != X2
      | k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ( X0 != X2
        & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ( X0 != X2
        & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,X1)
     => ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
        | ( X0 != X2
          & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_zfmisc_1)).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f35,f26])).

fof(f35,plain,(
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

fof(f1206,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK0,X0,k4_xboole_0(sK1,k4_xboole_0(sK1,X0))),k4_xboole_0(sK1,k4_xboole_0(sK1,X0)))
      | k4_xboole_0(sK0,k4_xboole_0(sK0,X0)) = k4_xboole_0(sK1,k4_xboole_0(sK1,X0)) ) ),
    inference(factoring,[],[f1143])).

fof(f1143,plain,(
    ! [X45,X44] :
      ( r2_hidden(sK4(sK0,X44,X45),X45)
      | r2_hidden(sK4(sK0,X44,X45),k4_xboole_0(sK1,k4_xboole_0(sK1,X44)))
      | k4_xboole_0(sK0,k4_xboole_0(sK0,X44)) = X45 ) ),
    inference(duplicate_literal_removal,[],[f1125])).

fof(f1125,plain,(
    ! [X45,X44] :
      ( k4_xboole_0(sK0,k4_xboole_0(sK0,X44)) = X45
      | r2_hidden(sK4(sK0,X44,X45),X45)
      | r2_hidden(sK4(sK0,X44,X45),k4_xboole_0(sK1,k4_xboole_0(sK1,X44)))
      | r2_hidden(sK4(sK0,X44,X45),X45)
      | k4_xboole_0(sK0,k4_xboole_0(sK0,X44)) = X45 ) ),
    inference(resolution,[],[f82,f765])).

fof(f765,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(sK0,X0,X1),X1)
      | r2_hidden(sK4(sK0,X0,X1),sK1)
      | k4_xboole_0(sK0,k4_xboole_0(sK0,X0)) = X1 ) ),
    inference(resolution,[],[f130,f20])).

fof(f20,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f130,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_tarski(X4,X7)
      | k4_xboole_0(X4,k4_xboole_0(X4,X5)) = X6
      | r2_hidden(sK4(X4,X5,X6),X6)
      | r2_hidden(sK4(X4,X5,X6),X7) ) ),
    inference(resolution,[],[f55,f27])).

fof(f27,plain,(
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

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f32,f26])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X3)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | r2_hidden(sK4(X0,X1,X2),X2)
      | r2_hidden(sK4(X0,X1,X2),k4_xboole_0(X3,k4_xboole_0(X3,X1))) ) ),
    inference(resolution,[],[f54,f58])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f36,f26])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f33,f26])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f1229,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(sK0,X0,k4_xboole_0(sK1,k4_xboole_0(sK1,X0))),sK0)
      | k4_xboole_0(sK0,k4_xboole_0(sK0,X0)) = k4_xboole_0(sK1,k4_xboole_0(sK1,X0)) ) ),
    inference(subsumption_resolution,[],[f1228,f89])).

fof(f89,plain,(
    ! [X14,X12,X15,X13] :
      ( r2_hidden(sK4(X12,X13,k4_xboole_0(X14,k4_xboole_0(X14,X15))),X13)
      | k4_xboole_0(X14,k4_xboole_0(X14,X15)) = k4_xboole_0(X12,k4_xboole_0(X12,X13))
      | r2_hidden(sK4(X12,X13,k4_xboole_0(X14,k4_xboole_0(X14,X15))),X15) ) ),
    inference(resolution,[],[f54,f59])).

fof(f1228,plain,(
    ! [X0] :
      ( k4_xboole_0(sK0,k4_xboole_0(sK0,X0)) = k4_xboole_0(sK1,k4_xboole_0(sK1,X0))
      | ~ r2_hidden(sK4(sK0,X0,k4_xboole_0(sK1,k4_xboole_0(sK1,X0))),X0)
      | ~ r2_hidden(sK4(sK0,X0,k4_xboole_0(sK1,k4_xboole_0(sK1,X0))),sK0) ) ),
    inference(duplicate_literal_removal,[],[f1214])).

fof(f1214,plain,(
    ! [X0] :
      ( k4_xboole_0(sK0,k4_xboole_0(sK0,X0)) = k4_xboole_0(sK1,k4_xboole_0(sK1,X0))
      | ~ r2_hidden(sK4(sK0,X0,k4_xboole_0(sK1,k4_xboole_0(sK1,X0))),X0)
      | ~ r2_hidden(sK4(sK0,X0,k4_xboole_0(sK1,k4_xboole_0(sK1,X0))),sK0)
      | k4_xboole_0(sK0,k4_xboole_0(sK0,X0)) = k4_xboole_0(sK1,k4_xboole_0(sK1,X0)) ) ),
    inference(resolution,[],[f1206,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X2)
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X0)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f31,f26])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:38:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (16755)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (16776)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.51  % (16768)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (16760)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (16767)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (16781)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.52  % (16762)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (16756)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (16770)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (16758)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (16761)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (16769)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (16759)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (16777)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (16784)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (16775)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (16763)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (16757)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (16782)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (16778)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.50/0.55  % (16765)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.50/0.55  % (16771)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.50/0.55  % (16772)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.50/0.56  % (16773)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.50/0.56  % (16766)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.50/0.56  % (16774)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.50/0.56  % (16783)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.50/0.57  % (16779)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.65/0.57  % (16780)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.65/0.57  % (16764)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 2.33/0.71  % (16761)Refutation found. Thanks to Tanya!
% 2.33/0.71  % SZS status Theorem for theBenchmark
% 2.90/0.74  % SZS output start Proof for theBenchmark
% 2.90/0.74  fof(f1343,plain,(
% 2.90/0.74    $false),
% 2.90/0.74    inference(subsumption_resolution,[],[f1331,f66])).
% 2.90/0.74  fof(f66,plain,(
% 2.90/0.74    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 2.90/0.74    inference(superposition,[],[f47,f48])).
% 2.90/0.74  fof(f48,plain,(
% 2.90/0.74    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 2.90/0.74    inference(definition_unfolding,[],[f21,f26,f46])).
% 2.90/0.74  fof(f46,plain,(
% 2.90/0.74    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.90/0.74    inference(definition_unfolding,[],[f24,f45])).
% 2.90/0.74  fof(f45,plain,(
% 2.90/0.74    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.90/0.74    inference(definition_unfolding,[],[f25,f44])).
% 2.90/0.74  fof(f44,plain,(
% 2.90/0.74    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.90/0.74    inference(definition_unfolding,[],[f28,f43])).
% 2.90/0.74  fof(f43,plain,(
% 2.90/0.74    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.90/0.74    inference(definition_unfolding,[],[f37,f42])).
% 2.90/0.74  fof(f42,plain,(
% 2.90/0.74    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.90/0.74    inference(definition_unfolding,[],[f38,f41])).
% 2.90/0.74  fof(f41,plain,(
% 2.90/0.74    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.90/0.74    inference(definition_unfolding,[],[f39,f40])).
% 2.90/0.74  fof(f40,plain,(
% 2.90/0.74    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 2.90/0.74    inference(cnf_transformation,[],[f10])).
% 2.90/0.74  fof(f10,axiom,(
% 2.90/0.74    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 2.90/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 2.90/0.74  fof(f39,plain,(
% 2.90/0.74    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 2.90/0.74    inference(cnf_transformation,[],[f9])).
% 2.90/0.74  fof(f9,axiom,(
% 2.90/0.74    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 2.90/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 2.90/0.74  fof(f38,plain,(
% 2.90/0.74    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.90/0.74    inference(cnf_transformation,[],[f8])).
% 2.90/0.74  fof(f8,axiom,(
% 2.90/0.74    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.90/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 2.90/0.74  fof(f37,plain,(
% 2.90/0.74    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.90/0.74    inference(cnf_transformation,[],[f7])).
% 2.90/0.74  fof(f7,axiom,(
% 2.90/0.74    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 2.90/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 2.90/0.74  fof(f28,plain,(
% 2.90/0.74    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.90/0.74    inference(cnf_transformation,[],[f6])).
% 2.90/0.74  fof(f6,axiom,(
% 2.90/0.74    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.90/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 2.90/0.74  fof(f25,plain,(
% 2.90/0.74    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.90/0.74    inference(cnf_transformation,[],[f5])).
% 2.90/0.74  fof(f5,axiom,(
% 2.90/0.74    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.90/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 2.90/0.74  fof(f24,plain,(
% 2.90/0.74    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.90/0.74    inference(cnf_transformation,[],[f4])).
% 2.90/0.74  fof(f4,axiom,(
% 2.90/0.74    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.90/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 2.90/0.74  fof(f26,plain,(
% 2.90/0.74    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.90/0.74    inference(cnf_transformation,[],[f3])).
% 2.90/0.74  fof(f3,axiom,(
% 2.90/0.74    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.90/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.90/0.74  fof(f21,plain,(
% 2.90/0.74    k3_xboole_0(sK1,sK2) = k1_tarski(sK3)),
% 2.90/0.74    inference(cnf_transformation,[],[f16])).
% 2.90/0.74  fof(f16,plain,(
% 2.90/0.74    ? [X0,X1,X2,X3] : (k1_tarski(X3) != k3_xboole_0(X0,X2) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1))),
% 2.90/0.74    inference(flattening,[],[f15])).
% 2.90/0.74  fof(f15,plain,(
% 2.90/0.74    ? [X0,X1,X2,X3] : (k1_tarski(X3) != k3_xboole_0(X0,X2) & (r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)))),
% 2.90/0.74    inference(ennf_transformation,[],[f13])).
% 2.90/0.74  fof(f13,negated_conjecture,(
% 2.90/0.74    ~! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k1_tarski(X3) = k3_xboole_0(X0,X2))),
% 2.90/0.74    inference(negated_conjecture,[],[f12])).
% 2.90/0.74  fof(f12,conjecture,(
% 2.90/0.74    ! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k1_tarski(X3) = k3_xboole_0(X0,X2))),
% 2.90/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_zfmisc_1)).
% 2.90/0.74  fof(f47,plain,(
% 2.90/0.74    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 2.90/0.74    inference(definition_unfolding,[],[f23,f46,f26])).
% 2.90/0.74  fof(f23,plain,(
% 2.90/0.74    k1_tarski(sK3) != k3_xboole_0(sK0,sK2)),
% 2.90/0.74    inference(cnf_transformation,[],[f16])).
% 2.90/0.74  fof(f1331,plain,(
% 2.90/0.74    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 2.90/0.74    inference(resolution,[],[f1229,f1230])).
% 2.90/0.74  fof(f1230,plain,(
% 2.90/0.74    r2_hidden(sK4(sK0,sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),sK0)),
% 2.90/0.74    inference(subsumption_resolution,[],[f1216,f66])).
% 2.90/0.74  fof(f1216,plain,(
% 2.90/0.74    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) | r2_hidden(sK4(sK0,sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),sK0)),
% 2.90/0.74    inference(resolution,[],[f1206,f425])).
% 2.90/0.74  fof(f425,plain,(
% 2.90/0.74    ( ! [X2] : (~r2_hidden(X2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) | r2_hidden(X2,sK0)) )),
% 2.90/0.74    inference(superposition,[],[f59,f379])).
% 2.90/0.74  fof(f379,plain,(
% 2.90/0.74    k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK0))),
% 2.90/0.74    inference(forward_demodulation,[],[f361,f48])).
% 2.90/0.74  fof(f361,plain,(
% 2.90/0.74    k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3) = k4_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),k4_xboole_0(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK3),sK0))),
% 2.90/0.74    inference(resolution,[],[f57,f22])).
% 2.90/0.74  fof(f22,plain,(
% 2.90/0.74    r2_hidden(sK3,sK0)),
% 2.90/0.74    inference(cnf_transformation,[],[f16])).
% 2.90/0.74  fof(f57,plain,(
% 2.90/0.74    ( ! [X2,X1] : (~r2_hidden(X2,X1) | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = k4_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k4_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),X1))) )),
% 2.90/0.74    inference(equality_resolution,[],[f49])).
% 2.90/0.74  fof(f49,plain,(
% 2.90/0.74    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | X0 != X2 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1))) )),
% 2.90/0.74    inference(definition_unfolding,[],[f30,f46,f26,f45])).
% 2.90/0.74  fof(f30,plain,(
% 2.90/0.74    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | X0 != X2 | k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)) )),
% 2.90/0.74    inference(cnf_transformation,[],[f19])).
% 2.90/0.74  fof(f19,plain,(
% 2.90/0.74    ! [X0,X1,X2] : (k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | (X0 != X2 & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 2.90/0.74    inference(flattening,[],[f18])).
% 2.90/0.74  fof(f18,plain,(
% 2.90/0.74    ! [X0,X1,X2] : ((k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | (X0 != X2 & r2_hidden(X2,X1))) | ~r2_hidden(X0,X1))),
% 2.90/0.74    inference(ennf_transformation,[],[f11])).
% 2.90/0.74  fof(f11,axiom,(
% 2.90/0.74    ! [X0,X1,X2] : (r2_hidden(X0,X1) => (k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | (X0 != X2 & r2_hidden(X2,X1))))),
% 2.90/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_zfmisc_1)).
% 2.90/0.74  fof(f59,plain,(
% 2.90/0.74    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r2_hidden(X3,X1)) )),
% 2.90/0.74    inference(equality_resolution,[],[f52])).
% 2.90/0.74  fof(f52,plain,(
% 2.90/0.74    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 2.90/0.74    inference(definition_unfolding,[],[f35,f26])).
% 2.90/0.74  fof(f35,plain,(
% 2.90/0.74    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 2.90/0.74    inference(cnf_transformation,[],[f2])).
% 2.90/0.74  fof(f2,axiom,(
% 2.90/0.74    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.90/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 2.90/0.74  fof(f1206,plain,(
% 2.90/0.74    ( ! [X0] : (r2_hidden(sK4(sK0,X0,k4_xboole_0(sK1,k4_xboole_0(sK1,X0))),k4_xboole_0(sK1,k4_xboole_0(sK1,X0))) | k4_xboole_0(sK0,k4_xboole_0(sK0,X0)) = k4_xboole_0(sK1,k4_xboole_0(sK1,X0))) )),
% 2.90/0.74    inference(factoring,[],[f1143])).
% 2.90/0.74  fof(f1143,plain,(
% 2.90/0.74    ( ! [X45,X44] : (r2_hidden(sK4(sK0,X44,X45),X45) | r2_hidden(sK4(sK0,X44,X45),k4_xboole_0(sK1,k4_xboole_0(sK1,X44))) | k4_xboole_0(sK0,k4_xboole_0(sK0,X44)) = X45) )),
% 2.90/0.74    inference(duplicate_literal_removal,[],[f1125])).
% 2.90/0.74  fof(f1125,plain,(
% 2.90/0.74    ( ! [X45,X44] : (k4_xboole_0(sK0,k4_xboole_0(sK0,X44)) = X45 | r2_hidden(sK4(sK0,X44,X45),X45) | r2_hidden(sK4(sK0,X44,X45),k4_xboole_0(sK1,k4_xboole_0(sK1,X44))) | r2_hidden(sK4(sK0,X44,X45),X45) | k4_xboole_0(sK0,k4_xboole_0(sK0,X44)) = X45) )),
% 2.90/0.74    inference(resolution,[],[f82,f765])).
% 2.90/0.74  fof(f765,plain,(
% 2.90/0.74    ( ! [X0,X1] : (r2_hidden(sK4(sK0,X0,X1),X1) | r2_hidden(sK4(sK0,X0,X1),sK1) | k4_xboole_0(sK0,k4_xboole_0(sK0,X0)) = X1) )),
% 2.90/0.74    inference(resolution,[],[f130,f20])).
% 2.90/0.74  fof(f20,plain,(
% 2.90/0.74    r1_tarski(sK0,sK1)),
% 2.90/0.74    inference(cnf_transformation,[],[f16])).
% 2.90/0.74  fof(f130,plain,(
% 2.90/0.74    ( ! [X6,X4,X7,X5] : (~r1_tarski(X4,X7) | k4_xboole_0(X4,k4_xboole_0(X4,X5)) = X6 | r2_hidden(sK4(X4,X5,X6),X6) | r2_hidden(sK4(X4,X5,X6),X7)) )),
% 2.90/0.74    inference(resolution,[],[f55,f27])).
% 2.90/0.74  fof(f27,plain,(
% 2.90/0.74    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r1_tarski(X0,X1) | r2_hidden(X2,X1)) )),
% 2.90/0.74    inference(cnf_transformation,[],[f17])).
% 2.90/0.74  fof(f17,plain,(
% 2.90/0.74    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 2.90/0.74    inference(ennf_transformation,[],[f14])).
% 2.90/0.74  fof(f14,plain,(
% 2.90/0.74    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.90/0.74    inference(unused_predicate_definition_removal,[],[f1])).
% 2.90/0.74  fof(f1,axiom,(
% 2.90/0.74    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.90/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 2.90/0.74  fof(f55,plain,(
% 2.90/0.74    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2) )),
% 2.90/0.74    inference(definition_unfolding,[],[f32,f26])).
% 2.90/0.74  fof(f32,plain,(
% 2.90/0.74    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 2.90/0.74    inference(cnf_transformation,[],[f2])).
% 2.90/0.74  fof(f82,plain,(
% 2.90/0.74    ( ! [X2,X0,X3,X1] : (~r2_hidden(sK4(X0,X1,X2),X3) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | r2_hidden(sK4(X0,X1,X2),X2) | r2_hidden(sK4(X0,X1,X2),k4_xboole_0(X3,k4_xboole_0(X3,X1)))) )),
% 2.90/0.74    inference(resolution,[],[f54,f58])).
% 2.90/0.74  fof(f58,plain,(
% 2.90/0.74    ( ! [X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | r2_hidden(X3,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 2.90/0.74    inference(equality_resolution,[],[f51])).
% 2.90/0.74  fof(f51,plain,(
% 2.90/0.74    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | r2_hidden(X3,X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 2.90/0.74    inference(definition_unfolding,[],[f36,f26])).
% 2.90/0.74  fof(f36,plain,(
% 2.90/0.74    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 2.90/0.74    inference(cnf_transformation,[],[f2])).
% 2.90/0.74  fof(f54,plain,(
% 2.90/0.74    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2) )),
% 2.90/0.74    inference(definition_unfolding,[],[f33,f26])).
% 2.90/0.74  fof(f33,plain,(
% 2.90/0.74    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 2.90/0.74    inference(cnf_transformation,[],[f2])).
% 2.90/0.74  fof(f1229,plain,(
% 2.90/0.74    ( ! [X0] : (~r2_hidden(sK4(sK0,X0,k4_xboole_0(sK1,k4_xboole_0(sK1,X0))),sK0) | k4_xboole_0(sK0,k4_xboole_0(sK0,X0)) = k4_xboole_0(sK1,k4_xboole_0(sK1,X0))) )),
% 2.90/0.74    inference(subsumption_resolution,[],[f1228,f89])).
% 2.90/0.74  fof(f89,plain,(
% 2.90/0.74    ( ! [X14,X12,X15,X13] : (r2_hidden(sK4(X12,X13,k4_xboole_0(X14,k4_xboole_0(X14,X15))),X13) | k4_xboole_0(X14,k4_xboole_0(X14,X15)) = k4_xboole_0(X12,k4_xboole_0(X12,X13)) | r2_hidden(sK4(X12,X13,k4_xboole_0(X14,k4_xboole_0(X14,X15))),X15)) )),
% 2.90/0.74    inference(resolution,[],[f54,f59])).
% 2.90/0.74  fof(f1228,plain,(
% 2.90/0.74    ( ! [X0] : (k4_xboole_0(sK0,k4_xboole_0(sK0,X0)) = k4_xboole_0(sK1,k4_xboole_0(sK1,X0)) | ~r2_hidden(sK4(sK0,X0,k4_xboole_0(sK1,k4_xboole_0(sK1,X0))),X0) | ~r2_hidden(sK4(sK0,X0,k4_xboole_0(sK1,k4_xboole_0(sK1,X0))),sK0)) )),
% 2.90/0.74    inference(duplicate_literal_removal,[],[f1214])).
% 2.90/0.74  fof(f1214,plain,(
% 2.90/0.74    ( ! [X0] : (k4_xboole_0(sK0,k4_xboole_0(sK0,X0)) = k4_xboole_0(sK1,k4_xboole_0(sK1,X0)) | ~r2_hidden(sK4(sK0,X0,k4_xboole_0(sK1,k4_xboole_0(sK1,X0))),X0) | ~r2_hidden(sK4(sK0,X0,k4_xboole_0(sK1,k4_xboole_0(sK1,X0))),sK0) | k4_xboole_0(sK0,k4_xboole_0(sK0,X0)) = k4_xboole_0(sK1,k4_xboole_0(sK1,X0))) )),
% 2.90/0.74    inference(resolution,[],[f1206,f56])).
% 2.90/0.74  fof(f56,plain,(
% 2.90/0.74    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X2) | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2) )),
% 2.90/0.74    inference(definition_unfolding,[],[f31,f26])).
% 2.90/0.74  fof(f31,plain,(
% 2.90/0.74    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 2.90/0.74    inference(cnf_transformation,[],[f2])).
% 2.90/0.74  % SZS output end Proof for theBenchmark
% 2.90/0.74  % (16761)------------------------------
% 2.90/0.74  % (16761)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.90/0.74  % (16761)Termination reason: Refutation
% 2.90/0.74  
% 2.90/0.74  % (16761)Memory used [KB]: 8187
% 2.90/0.74  % (16761)Time elapsed: 0.293 s
% 2.90/0.74  % (16761)------------------------------
% 2.90/0.74  % (16761)------------------------------
% 2.90/0.74  % (16754)Success in time 0.38 s
%------------------------------------------------------------------------------
