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
% DateTime   : Thu Dec  3 12:45:57 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 279 expanded)
%              Number of leaves         :   19 (  86 expanded)
%              Depth                    :   18
%              Number of atoms          :  162 ( 473 expanded)
%              Number of equality atoms :   76 ( 240 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f442,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f436])).

fof(f436,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f65,f395])).

fof(f395,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(forward_demodulation,[],[f394,f67])).

fof(f67,plain,(
    ! [X0] : k1_setfam_1(k1_enumset1(X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f38,f61])).

fof(f61,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f39,f42])).

fof(f42,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f39,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f38,plain,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

fof(f394,plain,(
    ! [X0,X1] : k1_setfam_1(k1_enumset1(X0,X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,k1_setfam_1(k1_enumset1(X1,X1,X1)))) ),
    inference(subsumption_resolution,[],[f393,f182])).

fof(f182,plain,(
    ! [X0] : k1_xboole_0 != k1_enumset1(X0,X0,X0) ),
    inference(backward_demodulation,[],[f85,f180])).

fof(f180,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f66,f175])).

fof(f175,plain,(
    ! [X4] : k4_xboole_0(X4,k1_xboole_0) = X4 ),
    inference(resolution,[],[f168,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f168,plain,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    inference(resolution,[],[f155,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f155,plain,(
    ! [X5] : ~ r2_hidden(X5,k1_xboole_0) ),
    inference(forward_demodulation,[],[f154,f88])).

fof(f88,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f84,f77])).

fof(f77,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(X0,k1_xboole_0),X0) ),
    inference(superposition,[],[f68,f66])).

fof(f68,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f40,f43])).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f84,plain,(
    ! [X4] :
      ( ~ r1_tarski(X4,k1_xboole_0)
      | k1_xboole_0 = X4 ) ),
    inference(resolution,[],[f52,f78])).

fof(f78,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(superposition,[],[f68,f66])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f154,plain,(
    ! [X5] : ~ r2_hidden(X5,k4_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(trivial_inequality_removal,[],[f150])).

fof(f150,plain,(
    ! [X5] :
      ( k1_xboole_0 != k1_xboole_0
      | ~ r2_hidden(X5,k4_xboole_0(k1_xboole_0,k1_xboole_0)) ) ),
    inference(superposition,[],[f93,f88])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) != X1
      | ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ) ),
    inference(resolution,[],[f70,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f46,f43])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f23,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f66,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f37,f43])).

fof(f37,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f85,plain,(
    ! [X0] : k1_enumset1(X0,X0,X0) != k4_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0)) ),
    inference(resolution,[],[f76,f54])).

fof(f76,plain,(
    ! [X1] : ~ r1_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1)) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r1_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f56,f61,f61])).

fof(f56,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ~ ( X0 = X1
        & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_zfmisc_1)).

fof(f393,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,k1_setfam_1(k1_enumset1(X1,X1,X1))))
      | k1_xboole_0 = k1_enumset1(X0,X0,X0) ) ),
    inference(subsumption_resolution,[],[f373,f182])).

fof(f373,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,k1_setfam_1(k1_enumset1(X1,X1,X1))))
      | k1_xboole_0 = k1_enumset1(X1,X1,X1)
      | k1_xboole_0 = k1_enumset1(X0,X0,X0) ) ),
    inference(superposition,[],[f140,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2))) ),
    inference(definition_unfolding,[],[f57,f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_tarski(k1_enumset1(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3))) ),
    inference(definition_unfolding,[],[f58,f60,f61])).

fof(f60,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f41,f42])).

fof(f41,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f58,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

fof(f57,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f140,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),X1))) = k4_xboole_0(X0,k4_xboole_0(X0,k1_setfam_1(X1)))
      | k1_xboole_0 = X1
      | k1_xboole_0 = k1_enumset1(X0,X0,X0) ) ),
    inference(superposition,[],[f72,f67])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k3_tarski(k1_enumset1(X0,X0,X1))) = k4_xboole_0(k1_setfam_1(X0),k4_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f55,f60,f43])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ~ ( k1_setfam_1(k2_xboole_0(X0,X1)) != k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_setfam_1)).

fof(f65,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k1_setfam_1(k1_enumset1(sK0,sK0,sK1)) ),
    inference(definition_unfolding,[],[f36,f43,f42])).

fof(f36,plain,(
    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f27])).

fof(f27,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1))
   => k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:46:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (17200)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.46  % (17192)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.51  % (17189)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.53  % (17207)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.53  % (17199)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.53  % (17197)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.53  % (17187)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.53  % (17197)Refutation not found, incomplete strategy% (17197)------------------------------
% 0.20/0.53  % (17197)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (17197)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (17197)Memory used [KB]: 10618
% 0.20/0.53  % (17197)Time elapsed: 0.133 s
% 0.20/0.53  % (17197)------------------------------
% 0.20/0.53  % (17197)------------------------------
% 0.20/0.53  % (17190)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.53  % (17199)Refutation not found, incomplete strategy% (17199)------------------------------
% 0.20/0.53  % (17199)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (17199)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (17199)Memory used [KB]: 1663
% 0.20/0.53  % (17199)Time elapsed: 0.091 s
% 0.20/0.53  % (17199)------------------------------
% 0.20/0.53  % (17199)------------------------------
% 0.20/0.53  % (17188)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  % (17185)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.54  % (17191)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.54  % (17210)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.54  % (17210)Refutation not found, incomplete strategy% (17210)------------------------------
% 0.20/0.54  % (17210)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (17210)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (17210)Memory used [KB]: 6140
% 0.20/0.54  % (17210)Time elapsed: 0.136 s
% 0.20/0.54  % (17210)------------------------------
% 0.20/0.54  % (17210)------------------------------
% 0.20/0.54  % (17186)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.54  % (17186)Refutation not found, incomplete strategy% (17186)------------------------------
% 0.20/0.54  % (17186)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (17186)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (17186)Memory used [KB]: 1663
% 0.20/0.54  % (17186)Time elapsed: 0.134 s
% 0.20/0.54  % (17186)------------------------------
% 0.20/0.54  % (17186)------------------------------
% 0.20/0.54  % (17213)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.54  % (17201)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.54  % (17214)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.54  % (17214)Refutation not found, incomplete strategy% (17214)------------------------------
% 0.20/0.54  % (17214)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (17208)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.54  % (17214)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (17214)Memory used [KB]: 1663
% 0.20/0.54  % (17214)Time elapsed: 0.001 s
% 0.20/0.54  % (17214)------------------------------
% 0.20/0.54  % (17214)------------------------------
% 0.20/0.54  % (17213)Refutation not found, incomplete strategy% (17213)------------------------------
% 0.20/0.54  % (17213)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (17213)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (17213)Memory used [KB]: 10618
% 0.20/0.54  % (17213)Time elapsed: 0.140 s
% 0.20/0.54  % (17213)------------------------------
% 0.20/0.54  % (17213)------------------------------
% 0.20/0.54  % (17201)Refutation not found, incomplete strategy% (17201)------------------------------
% 0.20/0.54  % (17201)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (17201)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (17201)Memory used [KB]: 10618
% 0.20/0.54  % (17201)Time elapsed: 0.138 s
% 0.20/0.54  % (17201)------------------------------
% 0.20/0.54  % (17201)------------------------------
% 0.20/0.54  % (17203)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.54  % (17205)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.54  % (17194)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.54  % (17203)Refutation not found, incomplete strategy% (17203)------------------------------
% 0.20/0.54  % (17203)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (17212)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.54  % (17198)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.54  % (17211)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.54  % (17202)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.55  % (17206)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.55  % (17202)Refutation not found, incomplete strategy% (17202)------------------------------
% 0.20/0.55  % (17202)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (17202)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (17202)Memory used [KB]: 1663
% 0.20/0.55  % (17202)Time elapsed: 0.136 s
% 0.20/0.55  % (17202)------------------------------
% 0.20/0.55  % (17202)------------------------------
% 0.20/0.55  % (17195)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.55  % (17196)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.55  % (17211)Refutation not found, incomplete strategy% (17211)------------------------------
% 0.20/0.55  % (17211)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (17204)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.55  % (17195)Refutation not found, incomplete strategy% (17195)------------------------------
% 0.20/0.55  % (17195)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (17211)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (17211)Memory used [KB]: 6140
% 0.20/0.55  % (17211)Time elapsed: 0.150 s
% 0.20/0.55  % (17211)------------------------------
% 0.20/0.55  % (17211)------------------------------
% 0.20/0.55  % (17212)Refutation not found, incomplete strategy% (17212)------------------------------
% 0.20/0.55  % (17212)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (17195)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (17195)Memory used [KB]: 10618
% 0.20/0.55  % (17195)Time elapsed: 0.150 s
% 0.20/0.55  % (17195)------------------------------
% 0.20/0.55  % (17195)------------------------------
% 0.20/0.55  % (17203)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (17203)Memory used [KB]: 1663
% 0.20/0.55  % (17203)Time elapsed: 0.138 s
% 0.20/0.55  % (17203)------------------------------
% 0.20/0.55  % (17203)------------------------------
% 0.20/0.55  % (17209)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.55  % (17193)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.55  % (17209)Refutation not found, incomplete strategy% (17209)------------------------------
% 0.20/0.55  % (17209)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (17196)Refutation not found, incomplete strategy% (17196)------------------------------
% 0.20/0.56  % (17196)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (17212)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (17212)Memory used [KB]: 6140
% 0.20/0.56  % (17212)Time elapsed: 0.148 s
% 0.20/0.56  % (17212)------------------------------
% 0.20/0.56  % (17212)------------------------------
% 0.20/0.56  % (17196)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (17196)Memory used [KB]: 6140
% 0.20/0.56  % (17196)Time elapsed: 0.149 s
% 0.20/0.56  % (17196)------------------------------
% 0.20/0.56  % (17196)------------------------------
% 0.20/0.56  % (17207)Refutation found. Thanks to Tanya!
% 0.20/0.56  % SZS status Theorem for theBenchmark
% 0.20/0.56  % (17209)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (17209)Memory used [KB]: 10618
% 0.20/0.56  % (17209)Time elapsed: 0.147 s
% 0.20/0.56  % (17209)------------------------------
% 0.20/0.56  % (17209)------------------------------
% 0.20/0.57  % SZS output start Proof for theBenchmark
% 0.20/0.57  fof(f442,plain,(
% 0.20/0.57    $false),
% 0.20/0.57    inference(trivial_inequality_removal,[],[f436])).
% 0.20/0.57  fof(f436,plain,(
% 0.20/0.57    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.20/0.57    inference(superposition,[],[f65,f395])).
% 0.20/0.57  fof(f395,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 0.20/0.57    inference(forward_demodulation,[],[f394,f67])).
% 0.20/0.57  fof(f67,plain,(
% 0.20/0.57    ( ! [X0] : (k1_setfam_1(k1_enumset1(X0,X0,X0)) = X0) )),
% 0.20/0.57    inference(definition_unfolding,[],[f38,f61])).
% 0.20/0.57  fof(f61,plain,(
% 0.20/0.57    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.20/0.57    inference(definition_unfolding,[],[f39,f42])).
% 0.20/0.57  fof(f42,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f12])).
% 0.20/0.57  fof(f12,axiom,(
% 0.20/0.57    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.57  fof(f39,plain,(
% 0.20/0.57    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f11])).
% 0.20/0.57  fof(f11,axiom,(
% 0.20/0.57    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.57  fof(f38,plain,(
% 0.20/0.57    ( ! [X0] : (k1_setfam_1(k1_tarski(X0)) = X0) )),
% 0.20/0.57    inference(cnf_transformation,[],[f17])).
% 0.20/0.57  fof(f17,axiom,(
% 0.20/0.57    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).
% 0.20/0.57  fof(f394,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k1_setfam_1(k1_enumset1(X0,X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,k1_setfam_1(k1_enumset1(X1,X1,X1))))) )),
% 0.20/0.57    inference(subsumption_resolution,[],[f393,f182])).
% 0.20/0.57  fof(f182,plain,(
% 0.20/0.57    ( ! [X0] : (k1_xboole_0 != k1_enumset1(X0,X0,X0)) )),
% 0.20/0.57    inference(backward_demodulation,[],[f85,f180])).
% 0.20/0.57  fof(f180,plain,(
% 0.20/0.57    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.20/0.57    inference(backward_demodulation,[],[f66,f175])).
% 0.20/0.57  fof(f175,plain,(
% 0.20/0.57    ( ! [X4] : (k4_xboole_0(X4,k1_xboole_0) = X4) )),
% 0.20/0.57    inference(resolution,[],[f168,f53])).
% 0.20/0.57  fof(f53,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 0.20/0.57    inference(cnf_transformation,[],[f35])).
% 0.20/0.57  fof(f35,plain,(
% 0.20/0.57    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.57    inference(nnf_transformation,[],[f8])).
% 0.20/0.57  fof(f8,axiom,(
% 0.20/0.57    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.20/0.57  fof(f168,plain,(
% 0.20/0.57    ( ! [X1] : (r1_xboole_0(X1,k1_xboole_0)) )),
% 0.20/0.57    inference(resolution,[],[f155,f48])).
% 0.20/0.57  fof(f48,plain,(
% 0.20/0.57    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f32])).
% 0.20/0.57  fof(f32,plain,(
% 0.20/0.57    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f31])).
% 0.20/0.57  fof(f31,plain,(
% 0.20/0.57    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f24,plain,(
% 0.20/0.57    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.57    inference(ennf_transformation,[],[f21])).
% 0.20/0.57  fof(f21,plain,(
% 0.20/0.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.57    inference(rectify,[],[f1])).
% 0.20/0.57  fof(f1,axiom,(
% 0.20/0.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.20/0.57  fof(f155,plain,(
% 0.20/0.57    ( ! [X5] : (~r2_hidden(X5,k1_xboole_0)) )),
% 0.20/0.57    inference(forward_demodulation,[],[f154,f88])).
% 0.20/0.57  fof(f88,plain,(
% 0.20/0.57    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.20/0.57    inference(resolution,[],[f84,f77])).
% 0.20/0.57  fof(f77,plain,(
% 0.20/0.57    ( ! [X0] : (r1_tarski(k4_xboole_0(X0,k1_xboole_0),X0)) )),
% 0.20/0.57    inference(superposition,[],[f68,f66])).
% 0.20/0.57  fof(f68,plain,(
% 0.20/0.57    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 0.20/0.57    inference(definition_unfolding,[],[f40,f43])).
% 0.20/0.57  fof(f43,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f7])).
% 0.20/0.57  fof(f7,axiom,(
% 0.20/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.57  fof(f40,plain,(
% 0.20/0.57    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f4])).
% 0.20/0.57  fof(f4,axiom,(
% 0.20/0.57    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.20/0.57  fof(f84,plain,(
% 0.20/0.57    ( ! [X4] : (~r1_tarski(X4,k1_xboole_0) | k1_xboole_0 = X4) )),
% 0.20/0.57    inference(resolution,[],[f52,f78])).
% 0.20/0.57  fof(f78,plain,(
% 0.20/0.57    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.57    inference(superposition,[],[f68,f66])).
% 0.20/0.57  fof(f52,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f34])).
% 0.20/0.57  fof(f34,plain,(
% 0.20/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.57    inference(flattening,[],[f33])).
% 0.20/0.57  fof(f33,plain,(
% 0.20/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.57    inference(nnf_transformation,[],[f3])).
% 0.20/0.57  fof(f3,axiom,(
% 0.20/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.57  fof(f154,plain,(
% 0.20/0.57    ( ! [X5] : (~r2_hidden(X5,k4_xboole_0(k1_xboole_0,k1_xboole_0))) )),
% 0.20/0.57    inference(trivial_inequality_removal,[],[f150])).
% 0.20/0.57  fof(f150,plain,(
% 0.20/0.57    ( ! [X5] : (k1_xboole_0 != k1_xboole_0 | ~r2_hidden(X5,k4_xboole_0(k1_xboole_0,k1_xboole_0))) )),
% 0.20/0.57    inference(superposition,[],[f93,f88])).
% 0.20/0.57  fof(f93,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) != X1 | ~r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) )),
% 0.20/0.57    inference(resolution,[],[f70,f54])).
% 0.20/0.57  fof(f54,plain,(
% 0.20/0.57    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 0.20/0.57    inference(cnf_transformation,[],[f35])).
% 0.20/0.57  fof(f70,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.20/0.57    inference(definition_unfolding,[],[f46,f43])).
% 0.20/0.57  fof(f46,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f30])).
% 0.20/0.57  fof(f30,plain,(
% 0.20/0.57    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.20/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f23,f29])).
% 0.20/0.57  fof(f29,plain,(
% 0.20/0.57    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f23,plain,(
% 0.20/0.57    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.20/0.57    inference(ennf_transformation,[],[f20])).
% 0.20/0.57  fof(f20,plain,(
% 0.20/0.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.57    inference(rectify,[],[f2])).
% 0.20/0.57  fof(f2,axiom,(
% 0.20/0.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.20/0.57  fof(f66,plain,(
% 0.20/0.57    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.20/0.57    inference(definition_unfolding,[],[f37,f43])).
% 0.20/0.57  fof(f37,plain,(
% 0.20/0.57    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f5])).
% 0.20/0.57  fof(f5,axiom,(
% 0.20/0.57    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.20/0.57  fof(f85,plain,(
% 0.20/0.57    ( ! [X0] : (k1_enumset1(X0,X0,X0) != k4_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0))) )),
% 0.20/0.57    inference(resolution,[],[f76,f54])).
% 0.20/0.57  fof(f76,plain,(
% 0.20/0.57    ( ! [X1] : (~r1_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1))) )),
% 0.20/0.57    inference(equality_resolution,[],[f73])).
% 0.20/0.57  fof(f73,plain,(
% 0.20/0.57    ( ! [X0,X1] : (X0 != X1 | ~r1_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1))) )),
% 0.20/0.57    inference(definition_unfolding,[],[f56,f61,f61])).
% 0.20/0.57  fof(f56,plain,(
% 0.20/0.57    ( ! [X0,X1] : (X0 != X1 | ~r1_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f26])).
% 0.20/0.57  fof(f26,plain,(
% 0.20/0.57    ! [X0,X1] : (X0 != X1 | ~r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.20/0.57    inference(ennf_transformation,[],[f15])).
% 0.20/0.57  fof(f15,axiom,(
% 0.20/0.57    ! [X0,X1] : ~(X0 = X1 & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_zfmisc_1)).
% 0.20/0.57  fof(f393,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k1_setfam_1(k1_enumset1(X0,X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,k1_setfam_1(k1_enumset1(X1,X1,X1)))) | k1_xboole_0 = k1_enumset1(X0,X0,X0)) )),
% 0.20/0.57    inference(subsumption_resolution,[],[f373,f182])).
% 0.20/0.57  fof(f373,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k1_setfam_1(k1_enumset1(X0,X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,k1_setfam_1(k1_enumset1(X1,X1,X1)))) | k1_xboole_0 = k1_enumset1(X1,X1,X1) | k1_xboole_0 = k1_enumset1(X0,X0,X0)) )),
% 0.20/0.57    inference(superposition,[],[f140,f64])).
% 0.20/0.57  fof(f64,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2)))) )),
% 0.20/0.57    inference(definition_unfolding,[],[f57,f62])).
% 0.20/0.57  fof(f62,plain,(
% 0.20/0.57    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_tarski(k1_enumset1(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3)))) )),
% 0.20/0.57    inference(definition_unfolding,[],[f58,f60,f61])).
% 0.20/0.57  fof(f60,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 0.20/0.57    inference(definition_unfolding,[],[f41,f42])).
% 0.20/0.57  fof(f41,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f14])).
% 0.20/0.57  fof(f14,axiom,(
% 0.20/0.57    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.20/0.57  fof(f58,plain,(
% 0.20/0.57    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f9])).
% 0.20/0.57  fof(f9,axiom,(
% 0.20/0.57    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).
% 0.20/0.57  fof(f57,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f13])).
% 0.20/0.57  fof(f13,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.57  fof(f140,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k1_setfam_1(k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),X1))) = k4_xboole_0(X0,k4_xboole_0(X0,k1_setfam_1(X1))) | k1_xboole_0 = X1 | k1_xboole_0 = k1_enumset1(X0,X0,X0)) )),
% 0.20/0.57    inference(superposition,[],[f72,f67])).
% 0.20/0.57  fof(f72,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k1_setfam_1(k3_tarski(k1_enumset1(X0,X0,X1))) = k4_xboole_0(k1_setfam_1(X0),k4_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.57    inference(definition_unfolding,[],[f55,f60,f43])).
% 0.20/0.57  fof(f55,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.57    inference(cnf_transformation,[],[f25])).
% 0.20/0.57  fof(f25,plain,(
% 0.20/0.57    ! [X0,X1] : (k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.20/0.57    inference(ennf_transformation,[],[f16])).
% 0.20/0.57  fof(f16,axiom,(
% 0.20/0.57    ! [X0,X1] : ~(k1_setfam_1(k2_xboole_0(X0,X1)) != k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_setfam_1)).
% 0.20/0.57  fof(f65,plain,(
% 0.20/0.57    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),
% 0.20/0.57    inference(definition_unfolding,[],[f36,f43,f42])).
% 0.20/0.57  fof(f36,plain,(
% 0.20/0.57    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1))),
% 0.20/0.57    inference(cnf_transformation,[],[f28])).
% 0.20/0.57  fof(f28,plain,(
% 0.20/0.57    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1))),
% 0.20/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f27])).
% 0.20/0.57  fof(f27,plain,(
% 0.20/0.57    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1)) => k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f22,plain,(
% 0.20/0.57    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1))),
% 0.20/0.57    inference(ennf_transformation,[],[f19])).
% 0.20/0.57  fof(f19,negated_conjecture,(
% 0.20/0.57    ~! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.20/0.57    inference(negated_conjecture,[],[f18])).
% 0.20/0.57  fof(f18,conjecture,(
% 0.20/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.57  % SZS output end Proof for theBenchmark
% 0.20/0.57  % (17207)------------------------------
% 0.20/0.57  % (17207)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (17207)Termination reason: Refutation
% 0.20/0.57  
% 0.20/0.57  % (17207)Memory used [KB]: 6524
% 0.20/0.57  % (17207)Time elapsed: 0.112 s
% 0.20/0.57  % (17207)------------------------------
% 0.20/0.57  % (17207)------------------------------
% 0.20/0.57  % (17183)Success in time 0.208 s
%------------------------------------------------------------------------------
