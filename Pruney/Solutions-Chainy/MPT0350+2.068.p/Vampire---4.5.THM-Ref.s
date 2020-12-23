%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:00 EST 2020

% Result     : Theorem 2.03s
% Output     : Refutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :  204 (68704 expanded)
%              Number of leaves         :   22 (20161 expanded)
%              Depth                    :   45
%              Number of atoms          :  300 (182590 expanded)
%              Number of equality atoms :  188 (56306 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1717,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1716,f115])).

fof(f115,plain,(
    sK0 != k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f80,f114])).

fof(f114,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1) ),
    inference(backward_demodulation,[],[f83,f106])).

fof(f106,plain,(
    sK1 = k3_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f93,f44])).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f93,plain,(
    sK1 = k3_xboole_0(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f89,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f89,plain,(
    r1_tarski(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f85,f79])).

fof(f79,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK2(X0,X1),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r1_tarski(sK2(X0,X1),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f36,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK2(X0,X1),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( r1_tarski(sK2(X0,X1),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f85,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f41,f39,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f39,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f30])).

fof(f30,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

fof(f41,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f83,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f39,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f57,f49])).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f57,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f80,plain,(
    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f40,f42])).

fof(f42,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f40,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f1716,plain,(
    sK0 = k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1715,f1662])).

fof(f1662,plain,(
    sK0 = k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1661,f377])).

fof(f377,plain,(
    sK0 = k5_xboole_0(k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f376,f194])).

fof(f194,plain,(
    sK0 = k3_tarski(k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(forward_demodulation,[],[f192,f43])).

fof(f43,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f192,plain,(
    k3_tarski(k2_enumset1(sK0,sK0,sK0,sK0)) = k5_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f73,f191])).

fof(f191,plain,(
    k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK0)) ),
    inference(superposition,[],[f71,f130])).

fof(f130,plain,(
    sK0 = k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)) ),
    inference(superposition,[],[f72,f106])).

fof(f72,plain,(
    ! [X0,X1] : k3_tarski(k2_enumset1(X0,X0,X0,k3_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f46,f70])).

fof(f70,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f47,f69])).

fof(f69,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f48,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f48,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f71,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f45,f49,f70])).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f73,plain,(
    ! [X0,X1] : k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f50,f70,f49])).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f376,plain,(
    k3_tarski(k2_enumset1(sK0,sK0,sK0,sK0)) = k5_xboole_0(k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f372,f315])).

fof(f315,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK0,k5_xboole_0(sK0,X0)) ),
    inference(backward_demodulation,[],[f193,f314])).

fof(f314,plain,(
    sK0 = k3_xboole_0(sK0,sK0) ),
    inference(forward_demodulation,[],[f313,f133])).

fof(f133,plain,(
    sK0 = k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)) ),
    inference(backward_demodulation,[],[f110,f130])).

fof(f110,plain,(
    k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)) ),
    inference(superposition,[],[f73,f93])).

fof(f313,plain,(
    k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)) = k3_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,sK1))) ),
    inference(forward_demodulation,[],[f310,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f310,plain,(
    k5_xboole_0(k5_xboole_0(sK0,sK1),sK1) = k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,sK1),sK1)) ),
    inference(superposition,[],[f124,f149])).

fof(f149,plain,(
    k5_xboole_0(sK0,sK1) = k3_xboole_0(k5_xboole_0(sK0,sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f145,f55])).

fof(f145,plain,(
    r1_tarski(k5_xboole_0(sK0,sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f122,f79])).

fof(f122,plain,(
    r2_hidden(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(backward_demodulation,[],[f102,f114])).

fof(f102,plain,(
    r2_hidden(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f41,f84,f51])).

fof(f84,plain,(
    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f39,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f124,plain,(
    ! [X0] : k5_xboole_0(k3_xboole_0(X0,sK0),sK1) = k3_xboole_0(sK0,k5_xboole_0(X0,sK1)) ),
    inference(forward_demodulation,[],[f108,f44])).

fof(f108,plain,(
    ! [X0] : k3_xboole_0(k5_xboole_0(X0,sK1),sK0) = k5_xboole_0(k3_xboole_0(X0,sK0),sK1) ),
    inference(superposition,[],[f67,f93])).

fof(f67,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).

fof(f193,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK0,k5_xboole_0(k3_xboole_0(sK0,sK0),X0)) ),
    inference(superposition,[],[f66,f191])).

fof(f372,plain,(
    k3_tarski(k2_enumset1(sK0,sK0,sK0,sK0)) = k5_xboole_0(sK0,k5_xboole_0(sK0,sK0)) ),
    inference(superposition,[],[f73,f314])).

fof(f1661,plain,(
    k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f1657,f1280])).

fof(f1280,plain,(
    ! [X0] : k5_xboole_0(sK1,k5_xboole_0(sK1,X0)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(backward_demodulation,[],[f807,f1272])).

fof(f1272,plain,(
    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK1) ),
    inference(forward_demodulation,[],[f1271,f186])).

fof(f186,plain,(
    k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK1)) ),
    inference(superposition,[],[f71,f111])).

fof(f111,plain,(
    sK1 = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(superposition,[],[f72,f93])).

fof(f1271,plain,(
    k5_xboole_0(sK1,k3_xboole_0(sK1,sK1)) = k3_xboole_0(k1_xboole_0,sK1) ),
    inference(forward_demodulation,[],[f1261,f793])).

fof(f793,plain,(
    k5_xboole_0(sK1,sK1) = k3_xboole_0(k1_xboole_0,sK1) ),
    inference(forward_demodulation,[],[f792,f44])).

fof(f792,plain,(
    k5_xboole_0(sK1,sK1) = k3_xboole_0(sK1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f790,f316])).

fof(f316,plain,(
    k1_xboole_0 = k5_xboole_0(sK0,sK0) ),
    inference(backward_demodulation,[],[f191,f314])).

fof(f790,plain,(
    k5_xboole_0(sK1,sK1) = k3_xboole_0(sK1,k5_xboole_0(sK0,sK0)) ),
    inference(superposition,[],[f131,f106])).

fof(f131,plain,(
    ! [X0] : k5_xboole_0(k3_xboole_0(X0,sK1),sK1) = k3_xboole_0(sK1,k5_xboole_0(X0,sK0)) ),
    inference(forward_demodulation,[],[f127,f44])).

fof(f127,plain,(
    ! [X0] : k3_xboole_0(k5_xboole_0(X0,sK0),sK1) = k5_xboole_0(k3_xboole_0(X0,sK1),sK1) ),
    inference(superposition,[],[f67,f106])).

fof(f1261,plain,(
    k5_xboole_0(sK1,k3_xboole_0(sK1,sK1)) = k5_xboole_0(sK1,sK1) ),
    inference(superposition,[],[f1246,f1216])).

fof(f1216,plain,(
    sK1 = k5_xboole_0(k1_xboole_0,k3_xboole_0(sK1,sK1)) ),
    inference(backward_demodulation,[],[f900,f1186])).

fof(f1186,plain,(
    sK1 = k5_xboole_0(k1_xboole_0,sK1) ),
    inference(superposition,[],[f606,f1176])).

fof(f1176,plain,(
    sK1 = k5_xboole_0(k1_xboole_0,k3_xboole_0(sK1,k3_xboole_0(sK1,sK1))) ),
    inference(forward_demodulation,[],[f1175,f72])).

fof(f1175,plain,(
    k3_tarski(k2_enumset1(sK1,sK1,sK1,k3_xboole_0(sK1,sK1))) = k5_xboole_0(k1_xboole_0,k3_xboole_0(sK1,k3_xboole_0(sK1,sK1))) ),
    inference(forward_demodulation,[],[f1168,f44])).

fof(f1168,plain,(
    k3_tarski(k2_enumset1(sK1,sK1,sK1,k3_xboole_0(sK1,sK1))) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(sK1,sK1),sK1)) ),
    inference(superposition,[],[f188,f73])).

fof(f188,plain,(
    ! [X0] : k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,sK1),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f66,f186])).

fof(f606,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f380,f315])).

fof(f380,plain,(
    ! [X0] : k5_xboole_0(sK0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK0,X0)) ),
    inference(superposition,[],[f66,f377])).

fof(f900,plain,(
    k5_xboole_0(k1_xboole_0,sK1) = k5_xboole_0(k1_xboole_0,k3_xboole_0(sK1,k5_xboole_0(k1_xboole_0,sK1))) ),
    inference(backward_demodulation,[],[f892,f899])).

fof(f899,plain,(
    k5_xboole_0(k1_xboole_0,sK1) = k4_subset_1(sK0,k5_xboole_0(k1_xboole_0,sK1),sK1) ),
    inference(forward_demodulation,[],[f896,f43])).

fof(f896,plain,(
    k4_subset_1(sK0,k5_xboole_0(k1_xboole_0,sK1),sK1) = k5_xboole_0(k5_xboole_0(k1_xboole_0,sK1),k1_xboole_0) ),
    inference(backward_demodulation,[],[f893,f870])).

fof(f870,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f132,f186])).

fof(f132,plain,(
    ! [X1] : k5_xboole_0(sK1,k3_xboole_0(X1,sK1)) = k3_xboole_0(sK1,k5_xboole_0(sK0,X1)) ),
    inference(forward_demodulation,[],[f128,f44])).

fof(f128,plain,(
    ! [X1] : k3_xboole_0(k5_xboole_0(sK0,X1),sK1) = k5_xboole_0(sK1,k3_xboole_0(X1,sK1)) ),
    inference(superposition,[],[f67,f106])).

fof(f893,plain,(
    k4_subset_1(sK0,k5_xboole_0(k1_xboole_0,sK1),sK1) = k5_xboole_0(k5_xboole_0(k1_xboole_0,sK1),k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f877,f517])).

fof(f517,plain,(
    ! [X0] : k5_xboole_0(sK0,X0) = k5_xboole_0(sK0,k5_xboole_0(k1_xboole_0,X0)) ),
    inference(forward_demodulation,[],[f507,f380])).

fof(f507,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,k5_xboole_0(sK0,X0)) = k5_xboole_0(sK0,k5_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f315,f315])).

fof(f877,plain,(
    k4_subset_1(sK0,k5_xboole_0(k1_xboole_0,sK1),sK1) = k5_xboole_0(k5_xboole_0(k1_xboole_0,sK1),k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(k1_xboole_0,sK1)))) ),
    inference(backward_demodulation,[],[f394,f867])).

fof(f867,plain,(
    ! [X0] : k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) = k3_xboole_0(sK1,k5_xboole_0(sK0,X0)) ),
    inference(superposition,[],[f132,f44])).

fof(f394,plain,(
    k4_subset_1(sK0,k5_xboole_0(k1_xboole_0,sK1),sK1) = k5_xboole_0(k5_xboole_0(k1_xboole_0,sK1),k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(k1_xboole_0,sK1)))) ),
    inference(forward_demodulation,[],[f387,f317])).

fof(f317,plain,(
    k3_subset_1(sK0,k5_xboole_0(sK0,sK1)) = k5_xboole_0(k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f216,f315])).

fof(f216,plain,(
    k3_subset_1(sK0,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f120,f207])).

fof(f207,plain,(
    k5_xboole_0(sK0,sK1) = k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f149,f44])).

fof(f120,plain,(
    k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK0,sK1))) = k3_subset_1(sK0,k5_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f100,f114])).

fof(f100,plain,(
    k5_xboole_0(sK0,k3_xboole_0(sK0,k3_subset_1(sK0,sK1))) = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f84,f74])).

fof(f387,plain,(
    k4_subset_1(sK0,k3_subset_1(sK0,k5_xboole_0(sK0,sK1)),sK1) = k5_xboole_0(k3_subset_1(sK0,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_subset_1(sK0,k5_xboole_0(sK0,sK1))))) ),
    inference(unit_resulting_resolution,[],[f116,f160])).

fof(f160,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
      | k4_subset_1(sK0,k3_subset_1(sK0,X1),sK1) = k5_xboole_0(k3_subset_1(sK0,X1),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_subset_1(sK0,X1)))) ) ),
    inference(forward_demodulation,[],[f156,f73])).

fof(f156,plain,(
    ! [X1] :
      ( k4_subset_1(sK0,k3_subset_1(sK0,X1),sK1) = k3_tarski(k2_enumset1(k3_subset_1(sK0,X1),k3_subset_1(sK0,X1),k3_subset_1(sK0,X1),sK1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f86,f56])).

fof(f86,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | k4_subset_1(sK0,X0,sK1) = k3_tarski(k2_enumset1(X0,X0,X0,sK1)) ) ),
    inference(resolution,[],[f39,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k2_enumset1(X1,X1,X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f68,f70])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f116,plain,(
    m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(backward_demodulation,[],[f84,f114])).

fof(f892,plain,(
    k4_subset_1(sK0,k5_xboole_0(k1_xboole_0,sK1),sK1) = k5_xboole_0(k1_xboole_0,k3_xboole_0(sK1,k5_xboole_0(k1_xboole_0,sK1))) ),
    inference(forward_demodulation,[],[f891,f606])).

fof(f891,plain,(
    k4_subset_1(sK0,k5_xboole_0(k1_xboole_0,sK1),sK1) = k5_xboole_0(k1_xboole_0,k3_xboole_0(sK1,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,sK1)))) ),
    inference(forward_demodulation,[],[f890,f315])).

fof(f890,plain,(
    k4_subset_1(sK0,k5_xboole_0(k1_xboole_0,sK1),sK1) = k5_xboole_0(k1_xboole_0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k1_xboole_0,sK1))))) ),
    inference(forward_demodulation,[],[f876,f867])).

fof(f876,plain,(
    k4_subset_1(sK0,k5_xboole_0(k1_xboole_0,sK1),sK1) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(k1_xboole_0,sK1))))) ),
    inference(backward_demodulation,[],[f698,f867])).

fof(f698,plain,(
    k4_subset_1(sK0,k5_xboole_0(k1_xboole_0,sK1),sK1) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(k1_xboole_0,sK1))))) ),
    inference(superposition,[],[f394,f66])).

fof(f1246,plain,(
    ! [X0] : k5_xboole_0(sK1,X0) = k5_xboole_0(sK1,k5_xboole_0(k1_xboole_0,X0)) ),
    inference(backward_demodulation,[],[f1240,f1244])).

fof(f1244,plain,(
    ! [X0] : k5_xboole_0(sK1,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,X0)) ),
    inference(superposition,[],[f66,f1186])).

fof(f1240,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,X0)) = k5_xboole_0(sK1,k5_xboole_0(k1_xboole_0,X0)) ),
    inference(forward_demodulation,[],[f1219,f188])).

fof(f1219,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,X0)) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,sK1),X0))) ),
    inference(backward_demodulation,[],[f904,f1186])).

fof(f904,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,X0)) = k5_xboole_0(k5_xboole_0(k1_xboole_0,sK1),k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,k5_xboole_0(k1_xboole_0,sK1)),X0))) ),
    inference(forward_demodulation,[],[f902,f66])).

fof(f902,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(k1_xboole_0,sK1),X0) = k5_xboole_0(k5_xboole_0(k1_xboole_0,sK1),k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,k5_xboole_0(k1_xboole_0,sK1)),X0))) ),
    inference(backward_demodulation,[],[f701,f899])).

fof(f701,plain,(
    ! [X0] : k5_xboole_0(k4_subset_1(sK0,k5_xboole_0(k1_xboole_0,sK1),sK1),X0) = k5_xboole_0(k5_xboole_0(k1_xboole_0,sK1),k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,k5_xboole_0(k1_xboole_0,sK1)),X0))) ),
    inference(forward_demodulation,[],[f700,f66])).

fof(f700,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(k1_xboole_0,sK1),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(k1_xboole_0,sK1))),X0)) = k5_xboole_0(k4_subset_1(sK0,k5_xboole_0(k1_xboole_0,sK1),sK1),X0) ),
    inference(superposition,[],[f66,f394])).

fof(f807,plain,(
    ! [X0] : k5_xboole_0(sK1,k5_xboole_0(sK1,X0)) = k5_xboole_0(k3_xboole_0(k1_xboole_0,sK1),X0) ),
    inference(superposition,[],[f66,f793])).

fof(f1657,plain,(
    k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,k5_xboole_0(sK1,sK0)) ),
    inference(superposition,[],[f1246,f1486])).

fof(f1486,plain,(
    k5_xboole_0(sK0,sK1) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK0)) ),
    inference(superposition,[],[f315,f1436])).

fof(f1436,plain,(
    sK1 = k5_xboole_0(sK0,k5_xboole_0(sK1,sK0)) ),
    inference(superposition,[],[f1402,f66])).

fof(f1402,plain,(
    sK1 = k5_xboole_0(k5_xboole_0(sK0,sK1),sK0) ),
    inference(backward_demodulation,[],[f1374,f1388])).

fof(f1388,plain,(
    sK1 = k3_xboole_0(sK1,sK1) ),
    inference(forward_demodulation,[],[f1387,f1186])).

fof(f1387,plain,(
    k3_xboole_0(sK1,sK1) = k5_xboole_0(k1_xboole_0,sK1) ),
    inference(forward_demodulation,[],[f1386,f1374])).

fof(f1386,plain,(
    k5_xboole_0(k1_xboole_0,sK1) = k5_xboole_0(k5_xboole_0(sK0,sK1),sK0) ),
    inference(forward_demodulation,[],[f1363,f43])).

fof(f1363,plain,(
    k5_xboole_0(k1_xboole_0,sK1) = k5_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK0,k1_xboole_0)) ),
    inference(superposition,[],[f918,f1273])).

fof(f1273,plain,(
    k1_xboole_0 = k5_xboole_0(sK1,sK1) ),
    inference(backward_demodulation,[],[f793,f1272])).

fof(f918,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,X0))) ),
    inference(forward_demodulation,[],[f917,f314])).

fof(f917,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(k3_xboole_0(sK0,sK0),k5_xboole_0(sK1,X0))) ),
    inference(forward_demodulation,[],[f916,f312])).

fof(f312,plain,(
    ! [X0,X1] : k5_xboole_0(k3_xboole_0(X0,sK0),k5_xboole_0(sK1,X1)) = k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(X0,sK1)),X1) ),
    inference(superposition,[],[f66,f124])).

fof(f916,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),X0)) ),
    inference(forward_demodulation,[],[f909,f44])).

fof(f909,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(k3_xboole_0(k5_xboole_0(sK0,sK1),sK0),X0)) ),
    inference(backward_demodulation,[],[f625,f905])).

fof(f905,plain,(
    sK0 = k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1) ),
    inference(forward_demodulation,[],[f897,f43])).

fof(f897,plain,(
    k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f888,f870])).

fof(f888,plain,(
    k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f887,f380])).

fof(f887,plain,(
    k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(k1_xboole_0,k5_xboole_0(sK0,sK1)))) ),
    inference(forward_demodulation,[],[f886,f315])).

fof(f886,plain,(
    k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK0,sK1))))) ),
    inference(forward_demodulation,[],[f874,f867])).

fof(f874,plain,(
    k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK0,sK1))))) ),
    inference(backward_demodulation,[],[f658,f867])).

fof(f658,plain,(
    k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))))) ),
    inference(superposition,[],[f287,f66])).

fof(f287,plain,(
    k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)))) ),
    inference(superposition,[],[f117,f73])).

fof(f117,plain,(
    k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1) = k3_tarski(k2_enumset1(k5_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1),sK1)) ),
    inference(backward_demodulation,[],[f96,f114])).

fof(f96,plain,(
    k4_subset_1(sK0,k3_subset_1(sK0,sK1),sK1) = k3_tarski(k2_enumset1(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1),sK1)) ),
    inference(unit_resulting_resolution,[],[f39,f84,f75])).

fof(f625,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(k3_xboole_0(k5_xboole_0(sK0,sK1),k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1)),X0)) ),
    inference(superposition,[],[f66,f289])).

fof(f289,plain,(
    k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(k5_xboole_0(sK0,sK1),k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1))) ),
    inference(superposition,[],[f71,f117])).

fof(f1374,plain,(
    k3_xboole_0(sK1,sK1) = k5_xboole_0(k5_xboole_0(sK0,sK1),sK0) ),
    inference(forward_demodulation,[],[f1373,f1186])).

fof(f1373,plain,(
    k3_xboole_0(sK1,k5_xboole_0(k1_xboole_0,sK1)) = k5_xboole_0(k5_xboole_0(sK0,sK1),sK0) ),
    inference(forward_demodulation,[],[f1372,f1312])).

fof(f1312,plain,(
    ! [X1] : k3_xboole_0(sK1,k5_xboole_0(k1_xboole_0,X1)) = k5_xboole_0(k1_xboole_0,k3_xboole_0(X1,sK1)) ),
    inference(forward_demodulation,[],[f1304,f44])).

fof(f1304,plain,(
    ! [X1] : k3_xboole_0(k5_xboole_0(k1_xboole_0,X1),sK1) = k5_xboole_0(k1_xboole_0,k3_xboole_0(X1,sK1)) ),
    inference(superposition,[],[f67,f1272])).

fof(f1372,plain,(
    k5_xboole_0(k1_xboole_0,k3_xboole_0(sK1,sK1)) = k5_xboole_0(k5_xboole_0(sK0,sK1),sK0) ),
    inference(forward_demodulation,[],[f1355,f43])).

fof(f1355,plain,(
    k5_xboole_0(k1_xboole_0,k3_xboole_0(sK1,sK1)) = k5_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK0,k1_xboole_0)) ),
    inference(superposition,[],[f918,f186])).

fof(f1715,plain,(
    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1714,f1388])).

fof(f1714,plain,(
    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,k5_xboole_0(sK0,k3_xboole_0(sK1,sK1))) ),
    inference(forward_demodulation,[],[f1713,f1020])).

fof(f1020,plain,(
    ! [X1] : k5_xboole_0(sK0,k3_xboole_0(X1,sK1)) = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(k1_xboole_0,X1))) ),
    inference(forward_demodulation,[],[f1019,f315])).

fof(f1019,plain,(
    ! [X1] : k5_xboole_0(sK0,k3_xboole_0(X1,sK1)) = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK0,X1)))) ),
    inference(forward_demodulation,[],[f1006,f867])).

fof(f1006,plain,(
    ! [X1] : k5_xboole_0(sK0,k3_xboole_0(X1,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK0,X1)))) ),
    inference(superposition,[],[f163,f132])).

fof(f163,plain,(
    ! [X0] : k5_xboole_0(sK0,X0) = k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,X0))) ),
    inference(forward_demodulation,[],[f162,f66])).

fof(f162,plain,(
    ! [X0] : k5_xboole_0(sK0,X0) = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,sK1),X0)) ),
    inference(superposition,[],[f66,f133])).

fof(f1713,plain,(
    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(k1_xboole_0,sK1)))) ),
    inference(forward_demodulation,[],[f1712,f315])).

fof(f1712,plain,(
    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK0,sK1))))) ),
    inference(forward_demodulation,[],[f1711,f132])).

fof(f1711,plain,(
    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK0,sK1),sK1)))) ),
    inference(forward_demodulation,[],[f1710,f1189])).

fof(f1189,plain,(
    sK1 = k3_subset_1(sK0,k5_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f317,f1186])).

fof(f1710,plain,(
    k4_subset_1(sK0,k3_subset_1(sK0,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK0,sK1)) = k5_xboole_0(k3_subset_1(sK0,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK0,sK1),k3_subset_1(sK0,k5_xboole_0(sK0,sK1)))))) ),
    inference(forward_demodulation,[],[f1697,f114])).

fof(f1697,plain,(
    k4_subset_1(sK0,k3_subset_1(sK0,k3_subset_1(sK0,sK1)),k5_xboole_0(sK0,sK1)) = k5_xboole_0(k3_subset_1(sK0,k3_subset_1(sK0,sK1)),k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK0,sK1),k3_subset_1(sK0,k3_subset_1(sK0,sK1)))))) ),
    inference(unit_resulting_resolution,[],[f39,f836])).

fof(f836,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
      | k4_subset_1(sK0,k3_subset_1(sK0,k3_subset_1(sK0,X1)),k5_xboole_0(sK0,sK1)) = k5_xboole_0(k3_subset_1(sK0,k3_subset_1(sK0,X1)),k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK0,sK1),k3_subset_1(sK0,k3_subset_1(sK0,X1)))))) ) ),
    inference(forward_demodulation,[],[f835,f66])).

fof(f835,plain,(
    ! [X1] :
      ( k4_subset_1(sK0,k3_subset_1(sK0,k3_subset_1(sK0,X1)),k5_xboole_0(sK0,sK1)) = k5_xboole_0(k3_subset_1(sK0,k3_subset_1(sK0,X1)),k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(k5_xboole_0(sK0,sK1),k3_subset_1(sK0,k3_subset_1(sK0,X1)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(sK0)) ) ),
    inference(forward_demodulation,[],[f824,f73])).

fof(f824,plain,(
    ! [X1] :
      ( k4_subset_1(sK0,k3_subset_1(sK0,k3_subset_1(sK0,X1)),k5_xboole_0(sK0,sK1)) = k3_tarski(k2_enumset1(k3_subset_1(sK0,k3_subset_1(sK0,X1)),k3_subset_1(sK0,k3_subset_1(sK0,X1)),k3_subset_1(sK0,k3_subset_1(sK0,X1)),k5_xboole_0(sK0,sK1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f302,f56])).

fof(f302,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
      | k4_subset_1(sK0,k3_subset_1(sK0,X1),k5_xboole_0(sK0,sK1)) = k3_tarski(k2_enumset1(k3_subset_1(sK0,X1),k3_subset_1(sK0,X1),k3_subset_1(sK0,X1),k5_xboole_0(sK0,sK1))) ) ),
    inference(resolution,[],[f123,f56])).

fof(f123,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | k4_subset_1(sK0,X0,k5_xboole_0(sK0,sK1)) = k3_tarski(k2_enumset1(X0,X0,X0,k5_xboole_0(sK0,sK1))) ) ),
    inference(backward_demodulation,[],[f103,f114])).

fof(f103,plain,(
    ! [X0] :
      ( k4_subset_1(sK0,X0,k3_subset_1(sK0,sK1)) = k3_tarski(k2_enumset1(X0,X0,X0,k3_subset_1(sK0,sK1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f84,f75])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:10:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (30365)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.50  % (30372)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.51  % (30366)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.51  % (30367)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.51  % (30368)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.51  % (30369)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (30378)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.27/0.52  % (30379)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.27/0.52  % (30391)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.27/0.52  % (30373)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.27/0.52  % (30381)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.27/0.52  % (30389)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.27/0.52  % (30390)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.27/0.52  % (30380)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.27/0.53  % (30395)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.27/0.53  % (30395)Refutation not found, incomplete strategy% (30395)------------------------------
% 1.27/0.53  % (30395)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.53  % (30395)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.53  
% 1.27/0.53  % (30395)Memory used [KB]: 10746
% 1.27/0.53  % (30395)Time elapsed: 0.123 s
% 1.27/0.53  % (30395)------------------------------
% 1.27/0.53  % (30395)------------------------------
% 1.27/0.53  % (30371)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.27/0.53  % (30387)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.27/0.53  % (30376)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.27/0.53  % (30388)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.27/0.53  % (30382)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.27/0.53  % (30370)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.37/0.54  % (30382)Refutation not found, incomplete strategy% (30382)------------------------------
% 1.37/0.54  % (30382)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.54  % (30382)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.54  
% 1.37/0.54  % (30382)Memory used [KB]: 10618
% 1.37/0.54  % (30382)Time elapsed: 0.099 s
% 1.37/0.54  % (30382)------------------------------
% 1.37/0.54  % (30382)------------------------------
% 1.37/0.54  % (30392)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.37/0.54  % (30393)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.37/0.54  % (30394)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.37/0.55  % (30384)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.37/0.55  % (30385)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.37/0.55  % (30386)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.37/0.55  % (30396)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.37/0.55  % (30396)Refutation not found, incomplete strategy% (30396)------------------------------
% 1.37/0.55  % (30396)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.55  % (30396)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.55  
% 1.37/0.55  % (30396)Memory used [KB]: 1663
% 1.37/0.55  % (30396)Time elapsed: 0.002 s
% 1.37/0.55  % (30396)------------------------------
% 1.37/0.55  % (30396)------------------------------
% 1.37/0.55  % (30375)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.37/0.55  % (30377)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.37/0.56  % (30376)Refutation not found, incomplete strategy% (30376)------------------------------
% 1.37/0.56  % (30376)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.56  % (30376)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.56  
% 1.37/0.56  % (30376)Memory used [KB]: 10746
% 1.37/0.56  % (30376)Time elapsed: 0.153 s
% 1.37/0.56  % (30376)------------------------------
% 1.37/0.56  % (30376)------------------------------
% 2.03/0.64  % (30377)Refutation found. Thanks to Tanya!
% 2.03/0.64  % SZS status Theorem for theBenchmark
% 2.03/0.64  % SZS output start Proof for theBenchmark
% 2.03/0.64  fof(f1717,plain,(
% 2.03/0.64    $false),
% 2.03/0.64    inference(subsumption_resolution,[],[f1716,f115])).
% 2.03/0.64  fof(f115,plain,(
% 2.03/0.64    sK0 != k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1))),
% 2.03/0.64    inference(backward_demodulation,[],[f80,f114])).
% 2.03/0.64  fof(f114,plain,(
% 2.03/0.64    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1)),
% 2.03/0.64    inference(backward_demodulation,[],[f83,f106])).
% 2.03/0.64  fof(f106,plain,(
% 2.03/0.64    sK1 = k3_xboole_0(sK0,sK1)),
% 2.03/0.64    inference(superposition,[],[f93,f44])).
% 2.03/0.64  fof(f44,plain,(
% 2.03/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f1])).
% 2.03/0.64  fof(f1,axiom,(
% 2.03/0.64    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.03/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.03/0.64  fof(f93,plain,(
% 2.03/0.64    sK1 = k3_xboole_0(sK1,sK0)),
% 2.03/0.64    inference(unit_resulting_resolution,[],[f89,f55])).
% 2.03/0.64  fof(f55,plain,(
% 2.03/0.64    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 2.03/0.64    inference(cnf_transformation,[],[f25])).
% 2.03/0.64  fof(f25,plain,(
% 2.03/0.64    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.03/0.64    inference(ennf_transformation,[],[f6])).
% 2.03/0.64  fof(f6,axiom,(
% 2.03/0.64    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.03/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.03/0.64  fof(f89,plain,(
% 2.03/0.64    r1_tarski(sK1,sK0)),
% 2.03/0.64    inference(unit_resulting_resolution,[],[f85,f79])).
% 2.03/0.64  fof(f79,plain,(
% 2.03/0.64    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 2.03/0.64    inference(equality_resolution,[],[f61])).
% 2.03/0.64  fof(f61,plain,(
% 2.03/0.64    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 2.03/0.64    inference(cnf_transformation,[],[f38])).
% 2.03/0.64  fof(f38,plain,(
% 2.03/0.64    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.03/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f36,f37])).
% 2.03/0.64  fof(f37,plain,(
% 2.03/0.64    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 2.03/0.64    introduced(choice_axiom,[])).
% 2.03/0.64  fof(f36,plain,(
% 2.03/0.64    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.03/0.64    inference(rectify,[],[f35])).
% 2.03/0.64  fof(f35,plain,(
% 2.03/0.64    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.03/0.64    inference(nnf_transformation,[],[f13])).
% 2.03/0.64  fof(f13,axiom,(
% 2.03/0.64    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 2.03/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 2.03/0.64  fof(f85,plain,(
% 2.03/0.64    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 2.03/0.64    inference(unit_resulting_resolution,[],[f41,f39,f51])).
% 2.03/0.64  fof(f51,plain,(
% 2.03/0.64    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f32])).
% 2.03/0.64  fof(f32,plain,(
% 2.03/0.64    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 2.03/0.64    inference(nnf_transformation,[],[f24])).
% 2.03/0.64  fof(f24,plain,(
% 2.03/0.64    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.03/0.64    inference(ennf_transformation,[],[f15])).
% 2.03/0.64  fof(f15,axiom,(
% 2.03/0.64    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.03/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 2.03/0.64  fof(f39,plain,(
% 2.03/0.64    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 2.03/0.64    inference(cnf_transformation,[],[f31])).
% 2.03/0.64  fof(f31,plain,(
% 2.03/0.64    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 2.03/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f30])).
% 2.03/0.64  fof(f30,plain,(
% 2.03/0.64    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 2.03/0.64    introduced(choice_axiom,[])).
% 2.03/0.64  fof(f23,plain,(
% 2.03/0.64    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.03/0.64    inference(ennf_transformation,[],[f22])).
% 2.03/0.64  fof(f22,negated_conjecture,(
% 2.03/0.64    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 2.03/0.64    inference(negated_conjecture,[],[f21])).
% 2.03/0.64  fof(f21,conjecture,(
% 2.03/0.64    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 2.03/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).
% 2.03/0.64  fof(f41,plain,(
% 2.03/0.64    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 2.03/0.64    inference(cnf_transformation,[],[f19])).
% 2.03/0.64  fof(f19,axiom,(
% 2.03/0.64    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 2.03/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 2.03/0.64  fof(f83,plain,(
% 2.03/0.64    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 2.03/0.64    inference(unit_resulting_resolution,[],[f39,f74])).
% 2.03/0.64  fof(f74,plain,(
% 2.03/0.64    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)) )),
% 2.03/0.64    inference(definition_unfolding,[],[f57,f49])).
% 2.03/0.64  fof(f49,plain,(
% 2.03/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.03/0.64    inference(cnf_transformation,[],[f3])).
% 2.03/0.64  fof(f3,axiom,(
% 2.03/0.64    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.03/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.03/0.64  fof(f57,plain,(
% 2.03/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.03/0.64    inference(cnf_transformation,[],[f27])).
% 2.03/0.64  fof(f27,plain,(
% 2.03/0.64    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.03/0.64    inference(ennf_transformation,[],[f17])).
% 2.03/0.64  fof(f17,axiom,(
% 2.03/0.64    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.03/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 2.03/0.64  fof(f80,plain,(
% 2.03/0.64    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 2.03/0.64    inference(forward_demodulation,[],[f40,f42])).
% 2.03/0.64  fof(f42,plain,(
% 2.03/0.64    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.03/0.64    inference(cnf_transformation,[],[f16])).
% 2.03/0.64  fof(f16,axiom,(
% 2.03/0.64    ! [X0] : k2_subset_1(X0) = X0),
% 2.03/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 2.03/0.64  fof(f40,plain,(
% 2.03/0.64    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 2.03/0.64    inference(cnf_transformation,[],[f31])).
% 2.03/0.64  fof(f1716,plain,(
% 2.03/0.64    sK0 = k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1))),
% 2.03/0.64    inference(forward_demodulation,[],[f1715,f1662])).
% 2.03/0.64  fof(f1662,plain,(
% 2.03/0.64    sK0 = k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))),
% 2.03/0.64    inference(forward_demodulation,[],[f1661,f377])).
% 2.03/0.64  fof(f377,plain,(
% 2.03/0.64    sK0 = k5_xboole_0(k1_xboole_0,sK0)),
% 2.03/0.64    inference(forward_demodulation,[],[f376,f194])).
% 2.03/0.64  fof(f194,plain,(
% 2.03/0.64    sK0 = k3_tarski(k2_enumset1(sK0,sK0,sK0,sK0))),
% 2.03/0.64    inference(forward_demodulation,[],[f192,f43])).
% 2.03/0.64  fof(f43,plain,(
% 2.03/0.64    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.03/0.64    inference(cnf_transformation,[],[f8])).
% 2.03/0.64  fof(f8,axiom,(
% 2.03/0.64    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.03/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 2.03/0.64  fof(f192,plain,(
% 2.03/0.64    k3_tarski(k2_enumset1(sK0,sK0,sK0,sK0)) = k5_xboole_0(sK0,k1_xboole_0)),
% 2.03/0.64    inference(superposition,[],[f73,f191])).
% 2.03/0.64  fof(f191,plain,(
% 2.03/0.64    k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK0))),
% 2.03/0.64    inference(superposition,[],[f71,f130])).
% 2.03/0.64  fof(f130,plain,(
% 2.03/0.64    sK0 = k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1))),
% 2.03/0.64    inference(superposition,[],[f72,f106])).
% 2.03/0.64  fof(f72,plain,(
% 2.03/0.64    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,k3_xboole_0(X0,X1))) = X0) )),
% 2.03/0.64    inference(definition_unfolding,[],[f46,f70])).
% 2.03/0.64  fof(f70,plain,(
% 2.03/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 2.03/0.64    inference(definition_unfolding,[],[f47,f69])).
% 2.03/0.64  fof(f69,plain,(
% 2.03/0.64    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.03/0.64    inference(definition_unfolding,[],[f48,f65])).
% 2.03/0.64  fof(f65,plain,(
% 2.03/0.64    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f12])).
% 2.03/0.64  fof(f12,axiom,(
% 2.03/0.64    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.03/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 2.03/0.64  fof(f48,plain,(
% 2.03/0.64    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f11])).
% 2.03/0.64  fof(f11,axiom,(
% 2.03/0.64    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.03/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.03/0.64  fof(f47,plain,(
% 2.03/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.03/0.64    inference(cnf_transformation,[],[f14])).
% 2.03/0.64  fof(f14,axiom,(
% 2.03/0.64    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.03/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.03/0.64  fof(f46,plain,(
% 2.03/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 2.03/0.64    inference(cnf_transformation,[],[f5])).
% 2.03/0.64  fof(f5,axiom,(
% 2.03/0.64    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 2.03/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 2.03/0.64  fof(f71,plain,(
% 2.03/0.64    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))))) )),
% 2.03/0.64    inference(definition_unfolding,[],[f45,f49,f70])).
% 2.03/0.64  fof(f45,plain,(
% 2.03/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 2.03/0.64    inference(cnf_transformation,[],[f7])).
% 2.03/0.64  fof(f7,axiom,(
% 2.03/0.64    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 2.03/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 2.03/0.64  fof(f73,plain,(
% 2.03/0.64    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 2.03/0.64    inference(definition_unfolding,[],[f50,f70,f49])).
% 2.03/0.64  fof(f50,plain,(
% 2.03/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.03/0.64    inference(cnf_transformation,[],[f10])).
% 2.03/0.64  fof(f10,axiom,(
% 2.03/0.64    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.03/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.03/0.64  fof(f376,plain,(
% 2.03/0.64    k3_tarski(k2_enumset1(sK0,sK0,sK0,sK0)) = k5_xboole_0(k1_xboole_0,sK0)),
% 2.03/0.64    inference(forward_demodulation,[],[f372,f315])).
% 2.03/0.64  fof(f315,plain,(
% 2.03/0.64    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK0,k5_xboole_0(sK0,X0))) )),
% 2.03/0.64    inference(backward_demodulation,[],[f193,f314])).
% 2.03/0.64  fof(f314,plain,(
% 2.03/0.64    sK0 = k3_xboole_0(sK0,sK0)),
% 2.03/0.64    inference(forward_demodulation,[],[f313,f133])).
% 2.03/0.64  fof(f133,plain,(
% 2.03/0.64    sK0 = k5_xboole_0(sK0,k5_xboole_0(sK1,sK1))),
% 2.03/0.64    inference(backward_demodulation,[],[f110,f130])).
% 2.03/0.64  fof(f110,plain,(
% 2.03/0.64    k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK1,sK1))),
% 2.03/0.64    inference(superposition,[],[f73,f93])).
% 2.03/0.64  fof(f313,plain,(
% 2.03/0.64    k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)) = k3_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)))),
% 2.03/0.64    inference(forward_demodulation,[],[f310,f66])).
% 2.03/0.64  fof(f66,plain,(
% 2.03/0.64    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.03/0.65    inference(cnf_transformation,[],[f9])).
% 2.03/0.65  fof(f9,axiom,(
% 2.03/0.65    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.03/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.03/0.65  fof(f310,plain,(
% 2.03/0.65    k5_xboole_0(k5_xboole_0(sK0,sK1),sK1) = k3_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,sK1),sK1))),
% 2.03/0.65    inference(superposition,[],[f124,f149])).
% 2.03/0.65  fof(f149,plain,(
% 2.03/0.65    k5_xboole_0(sK0,sK1) = k3_xboole_0(k5_xboole_0(sK0,sK1),sK0)),
% 2.03/0.65    inference(unit_resulting_resolution,[],[f145,f55])).
% 2.03/0.65  fof(f145,plain,(
% 2.03/0.65    r1_tarski(k5_xboole_0(sK0,sK1),sK0)),
% 2.03/0.65    inference(unit_resulting_resolution,[],[f122,f79])).
% 2.03/0.65  fof(f122,plain,(
% 2.03/0.65    r2_hidden(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 2.03/0.65    inference(backward_demodulation,[],[f102,f114])).
% 2.03/0.65  fof(f102,plain,(
% 2.03/0.65    r2_hidden(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 2.03/0.65    inference(unit_resulting_resolution,[],[f41,f84,f51])).
% 2.03/0.65  fof(f84,plain,(
% 2.03/0.65    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 2.03/0.65    inference(unit_resulting_resolution,[],[f39,f56])).
% 2.03/0.65  fof(f56,plain,(
% 2.03/0.65    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.03/0.65    inference(cnf_transformation,[],[f26])).
% 2.03/0.65  fof(f26,plain,(
% 2.03/0.65    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.03/0.65    inference(ennf_transformation,[],[f18])).
% 2.03/0.65  fof(f18,axiom,(
% 2.03/0.65    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.03/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 2.03/0.65  fof(f124,plain,(
% 2.03/0.65    ( ! [X0] : (k5_xboole_0(k3_xboole_0(X0,sK0),sK1) = k3_xboole_0(sK0,k5_xboole_0(X0,sK1))) )),
% 2.03/0.65    inference(forward_demodulation,[],[f108,f44])).
% 2.03/0.65  fof(f108,plain,(
% 2.03/0.65    ( ! [X0] : (k3_xboole_0(k5_xboole_0(X0,sK1),sK0) = k5_xboole_0(k3_xboole_0(X0,sK0),sK1)) )),
% 2.03/0.65    inference(superposition,[],[f67,f93])).
% 2.03/0.65  fof(f67,plain,(
% 2.03/0.65    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) )),
% 2.03/0.65    inference(cnf_transformation,[],[f4])).
% 2.03/0.65  fof(f4,axiom,(
% 2.03/0.65    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 2.03/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).
% 2.03/0.65  fof(f193,plain,(
% 2.03/0.65    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK0,k5_xboole_0(k3_xboole_0(sK0,sK0),X0))) )),
% 2.03/0.65    inference(superposition,[],[f66,f191])).
% 2.03/0.65  fof(f372,plain,(
% 2.03/0.65    k3_tarski(k2_enumset1(sK0,sK0,sK0,sK0)) = k5_xboole_0(sK0,k5_xboole_0(sK0,sK0))),
% 2.03/0.65    inference(superposition,[],[f73,f314])).
% 2.03/0.65  fof(f1661,plain,(
% 2.03/0.65    k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(k1_xboole_0,sK0)),
% 2.03/0.65    inference(forward_demodulation,[],[f1657,f1280])).
% 2.03/0.65  fof(f1280,plain,(
% 2.03/0.65    ( ! [X0] : (k5_xboole_0(sK1,k5_xboole_0(sK1,X0)) = k5_xboole_0(k1_xboole_0,X0)) )),
% 2.03/0.65    inference(backward_demodulation,[],[f807,f1272])).
% 2.03/0.65  fof(f1272,plain,(
% 2.03/0.65    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK1)),
% 2.03/0.65    inference(forward_demodulation,[],[f1271,f186])).
% 2.03/0.65  fof(f186,plain,(
% 2.03/0.65    k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK1))),
% 2.03/0.65    inference(superposition,[],[f71,f111])).
% 2.03/0.65  fof(f111,plain,(
% 2.03/0.65    sK1 = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK1))),
% 2.03/0.65    inference(superposition,[],[f72,f93])).
% 2.03/0.65  fof(f1271,plain,(
% 2.03/0.65    k5_xboole_0(sK1,k3_xboole_0(sK1,sK1)) = k3_xboole_0(k1_xboole_0,sK1)),
% 2.03/0.65    inference(forward_demodulation,[],[f1261,f793])).
% 2.03/0.65  fof(f793,plain,(
% 2.03/0.65    k5_xboole_0(sK1,sK1) = k3_xboole_0(k1_xboole_0,sK1)),
% 2.03/0.65    inference(forward_demodulation,[],[f792,f44])).
% 2.03/0.65  fof(f792,plain,(
% 2.03/0.65    k5_xboole_0(sK1,sK1) = k3_xboole_0(sK1,k1_xboole_0)),
% 2.03/0.65    inference(forward_demodulation,[],[f790,f316])).
% 2.03/0.65  fof(f316,plain,(
% 2.03/0.65    k1_xboole_0 = k5_xboole_0(sK0,sK0)),
% 2.03/0.65    inference(backward_demodulation,[],[f191,f314])).
% 2.03/0.65  fof(f790,plain,(
% 2.03/0.65    k5_xboole_0(sK1,sK1) = k3_xboole_0(sK1,k5_xboole_0(sK0,sK0))),
% 2.03/0.65    inference(superposition,[],[f131,f106])).
% 2.03/0.65  fof(f131,plain,(
% 2.03/0.65    ( ! [X0] : (k5_xboole_0(k3_xboole_0(X0,sK1),sK1) = k3_xboole_0(sK1,k5_xboole_0(X0,sK0))) )),
% 2.03/0.65    inference(forward_demodulation,[],[f127,f44])).
% 2.03/0.65  fof(f127,plain,(
% 2.03/0.65    ( ! [X0] : (k3_xboole_0(k5_xboole_0(X0,sK0),sK1) = k5_xboole_0(k3_xboole_0(X0,sK1),sK1)) )),
% 2.03/0.65    inference(superposition,[],[f67,f106])).
% 2.03/0.65  fof(f1261,plain,(
% 2.03/0.65    k5_xboole_0(sK1,k3_xboole_0(sK1,sK1)) = k5_xboole_0(sK1,sK1)),
% 2.03/0.65    inference(superposition,[],[f1246,f1216])).
% 2.03/0.65  fof(f1216,plain,(
% 2.03/0.65    sK1 = k5_xboole_0(k1_xboole_0,k3_xboole_0(sK1,sK1))),
% 2.03/0.65    inference(backward_demodulation,[],[f900,f1186])).
% 2.03/0.65  fof(f1186,plain,(
% 2.03/0.65    sK1 = k5_xboole_0(k1_xboole_0,sK1)),
% 2.03/0.65    inference(superposition,[],[f606,f1176])).
% 2.03/0.65  fof(f1176,plain,(
% 2.03/0.65    sK1 = k5_xboole_0(k1_xboole_0,k3_xboole_0(sK1,k3_xboole_0(sK1,sK1)))),
% 2.03/0.65    inference(forward_demodulation,[],[f1175,f72])).
% 2.03/0.65  fof(f1175,plain,(
% 2.03/0.65    k3_tarski(k2_enumset1(sK1,sK1,sK1,k3_xboole_0(sK1,sK1))) = k5_xboole_0(k1_xboole_0,k3_xboole_0(sK1,k3_xboole_0(sK1,sK1)))),
% 2.03/0.65    inference(forward_demodulation,[],[f1168,f44])).
% 2.03/0.65  fof(f1168,plain,(
% 2.03/0.65    k3_tarski(k2_enumset1(sK1,sK1,sK1,k3_xboole_0(sK1,sK1))) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(sK1,sK1),sK1))),
% 2.03/0.65    inference(superposition,[],[f188,f73])).
% 2.03/0.65  fof(f188,plain,(
% 2.03/0.65    ( ! [X0] : (k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,sK1),X0)) = k5_xboole_0(k1_xboole_0,X0)) )),
% 2.03/0.65    inference(superposition,[],[f66,f186])).
% 2.03/0.65  fof(f606,plain,(
% 2.03/0.65    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0))) )),
% 2.03/0.65    inference(superposition,[],[f380,f315])).
% 2.03/0.65  fof(f380,plain,(
% 2.03/0.65    ( ! [X0] : (k5_xboole_0(sK0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK0,X0))) )),
% 2.03/0.65    inference(superposition,[],[f66,f377])).
% 2.03/0.65  fof(f900,plain,(
% 2.03/0.65    k5_xboole_0(k1_xboole_0,sK1) = k5_xboole_0(k1_xboole_0,k3_xboole_0(sK1,k5_xboole_0(k1_xboole_0,sK1)))),
% 2.03/0.65    inference(backward_demodulation,[],[f892,f899])).
% 2.03/0.65  fof(f899,plain,(
% 2.03/0.65    k5_xboole_0(k1_xboole_0,sK1) = k4_subset_1(sK0,k5_xboole_0(k1_xboole_0,sK1),sK1)),
% 2.03/0.65    inference(forward_demodulation,[],[f896,f43])).
% 2.03/0.65  fof(f896,plain,(
% 2.03/0.65    k4_subset_1(sK0,k5_xboole_0(k1_xboole_0,sK1),sK1) = k5_xboole_0(k5_xboole_0(k1_xboole_0,sK1),k1_xboole_0)),
% 2.03/0.65    inference(backward_demodulation,[],[f893,f870])).
% 2.03/0.65  fof(f870,plain,(
% 2.03/0.65    k1_xboole_0 = k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))),
% 2.03/0.65    inference(superposition,[],[f132,f186])).
% 2.03/0.65  fof(f132,plain,(
% 2.03/0.65    ( ! [X1] : (k5_xboole_0(sK1,k3_xboole_0(X1,sK1)) = k3_xboole_0(sK1,k5_xboole_0(sK0,X1))) )),
% 2.03/0.65    inference(forward_demodulation,[],[f128,f44])).
% 2.03/0.65  fof(f128,plain,(
% 2.03/0.65    ( ! [X1] : (k3_xboole_0(k5_xboole_0(sK0,X1),sK1) = k5_xboole_0(sK1,k3_xboole_0(X1,sK1))) )),
% 2.03/0.65    inference(superposition,[],[f67,f106])).
% 2.03/0.65  fof(f893,plain,(
% 2.03/0.65    k4_subset_1(sK0,k5_xboole_0(k1_xboole_0,sK1),sK1) = k5_xboole_0(k5_xboole_0(k1_xboole_0,sK1),k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)))),
% 2.03/0.65    inference(forward_demodulation,[],[f877,f517])).
% 2.03/0.65  fof(f517,plain,(
% 2.03/0.65    ( ! [X0] : (k5_xboole_0(sK0,X0) = k5_xboole_0(sK0,k5_xboole_0(k1_xboole_0,X0))) )),
% 2.03/0.65    inference(forward_demodulation,[],[f507,f380])).
% 2.03/0.65  fof(f507,plain,(
% 2.03/0.65    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(sK0,X0)) = k5_xboole_0(sK0,k5_xboole_0(k1_xboole_0,X0))) )),
% 2.03/0.65    inference(superposition,[],[f315,f315])).
% 2.03/0.65  fof(f877,plain,(
% 2.03/0.65    k4_subset_1(sK0,k5_xboole_0(k1_xboole_0,sK1),sK1) = k5_xboole_0(k5_xboole_0(k1_xboole_0,sK1),k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(k1_xboole_0,sK1))))),
% 2.03/0.65    inference(backward_demodulation,[],[f394,f867])).
% 2.03/0.65  fof(f867,plain,(
% 2.03/0.65    ( ! [X0] : (k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) = k3_xboole_0(sK1,k5_xboole_0(sK0,X0))) )),
% 2.03/0.65    inference(superposition,[],[f132,f44])).
% 2.03/0.65  fof(f394,plain,(
% 2.03/0.65    k4_subset_1(sK0,k5_xboole_0(k1_xboole_0,sK1),sK1) = k5_xboole_0(k5_xboole_0(k1_xboole_0,sK1),k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(k1_xboole_0,sK1))))),
% 2.03/0.65    inference(forward_demodulation,[],[f387,f317])).
% 2.03/0.65  fof(f317,plain,(
% 2.03/0.65    k3_subset_1(sK0,k5_xboole_0(sK0,sK1)) = k5_xboole_0(k1_xboole_0,sK1)),
% 2.03/0.65    inference(backward_demodulation,[],[f216,f315])).
% 2.03/0.65  fof(f216,plain,(
% 2.03/0.65    k3_subset_1(sK0,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK0,sK1))),
% 2.03/0.65    inference(backward_demodulation,[],[f120,f207])).
% 2.03/0.65  fof(f207,plain,(
% 2.03/0.65    k5_xboole_0(sK0,sK1) = k3_xboole_0(sK0,k5_xboole_0(sK0,sK1))),
% 2.03/0.65    inference(superposition,[],[f149,f44])).
% 2.03/0.65  fof(f120,plain,(
% 2.03/0.65    k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK0,sK1))) = k3_subset_1(sK0,k5_xboole_0(sK0,sK1))),
% 2.03/0.65    inference(backward_demodulation,[],[f100,f114])).
% 2.03/0.65  fof(f100,plain,(
% 2.03/0.65    k5_xboole_0(sK0,k3_xboole_0(sK0,k3_subset_1(sK0,sK1))) = k3_subset_1(sK0,k3_subset_1(sK0,sK1))),
% 2.03/0.65    inference(unit_resulting_resolution,[],[f84,f74])).
% 2.03/0.65  fof(f387,plain,(
% 2.03/0.65    k4_subset_1(sK0,k3_subset_1(sK0,k5_xboole_0(sK0,sK1)),sK1) = k5_xboole_0(k3_subset_1(sK0,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_subset_1(sK0,k5_xboole_0(sK0,sK1)))))),
% 2.03/0.65    inference(unit_resulting_resolution,[],[f116,f160])).
% 2.03/0.65  fof(f160,plain,(
% 2.03/0.65    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(sK0)) | k4_subset_1(sK0,k3_subset_1(sK0,X1),sK1) = k5_xboole_0(k3_subset_1(sK0,X1),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_subset_1(sK0,X1))))) )),
% 2.03/0.65    inference(forward_demodulation,[],[f156,f73])).
% 2.03/0.65  fof(f156,plain,(
% 2.03/0.65    ( ! [X1] : (k4_subset_1(sK0,k3_subset_1(sK0,X1),sK1) = k3_tarski(k2_enumset1(k3_subset_1(sK0,X1),k3_subset_1(sK0,X1),k3_subset_1(sK0,X1),sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(sK0))) )),
% 2.03/0.65    inference(resolution,[],[f86,f56])).
% 2.03/0.65  fof(f86,plain,(
% 2.03/0.65    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | k4_subset_1(sK0,X0,sK1) = k3_tarski(k2_enumset1(X0,X0,X0,sK1))) )),
% 2.03/0.65    inference(resolution,[],[f39,f75])).
% 2.03/0.65  fof(f75,plain,(
% 2.03/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k2_enumset1(X1,X1,X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.03/0.65    inference(definition_unfolding,[],[f68,f70])).
% 2.03/0.65  fof(f68,plain,(
% 2.03/0.65    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.03/0.65    inference(cnf_transformation,[],[f29])).
% 2.03/0.65  fof(f29,plain,(
% 2.03/0.65    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.03/0.65    inference(flattening,[],[f28])).
% 2.03/0.65  fof(f28,plain,(
% 2.03/0.65    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.03/0.65    inference(ennf_transformation,[],[f20])).
% 2.03/0.65  fof(f20,axiom,(
% 2.03/0.65    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 2.03/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 2.03/0.65  fof(f116,plain,(
% 2.03/0.65    m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 2.03/0.65    inference(backward_demodulation,[],[f84,f114])).
% 2.03/0.65  fof(f892,plain,(
% 2.03/0.65    k4_subset_1(sK0,k5_xboole_0(k1_xboole_0,sK1),sK1) = k5_xboole_0(k1_xboole_0,k3_xboole_0(sK1,k5_xboole_0(k1_xboole_0,sK1)))),
% 2.03/0.65    inference(forward_demodulation,[],[f891,f606])).
% 2.03/0.65  fof(f891,plain,(
% 2.03/0.65    k4_subset_1(sK0,k5_xboole_0(k1_xboole_0,sK1),sK1) = k5_xboole_0(k1_xboole_0,k3_xboole_0(sK1,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,sK1))))),
% 2.03/0.65    inference(forward_demodulation,[],[f890,f315])).
% 2.03/0.65  fof(f890,plain,(
% 2.03/0.65    k4_subset_1(sK0,k5_xboole_0(k1_xboole_0,sK1),sK1) = k5_xboole_0(k1_xboole_0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k1_xboole_0,sK1)))))),
% 2.03/0.65    inference(forward_demodulation,[],[f876,f867])).
% 2.03/0.65  fof(f876,plain,(
% 2.03/0.65    k4_subset_1(sK0,k5_xboole_0(k1_xboole_0,sK1),sK1) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(k1_xboole_0,sK1)))))),
% 2.03/0.65    inference(backward_demodulation,[],[f698,f867])).
% 2.03/0.65  fof(f698,plain,(
% 2.03/0.65    k4_subset_1(sK0,k5_xboole_0(k1_xboole_0,sK1),sK1) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(k1_xboole_0,sK1)))))),
% 2.03/0.65    inference(superposition,[],[f394,f66])).
% 2.03/0.65  fof(f1246,plain,(
% 2.03/0.65    ( ! [X0] : (k5_xboole_0(sK1,X0) = k5_xboole_0(sK1,k5_xboole_0(k1_xboole_0,X0))) )),
% 2.03/0.65    inference(backward_demodulation,[],[f1240,f1244])).
% 2.03/0.65  fof(f1244,plain,(
% 2.03/0.65    ( ! [X0] : (k5_xboole_0(sK1,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,X0))) )),
% 2.03/0.65    inference(superposition,[],[f66,f1186])).
% 2.03/0.65  fof(f1240,plain,(
% 2.03/0.65    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,X0)) = k5_xboole_0(sK1,k5_xboole_0(k1_xboole_0,X0))) )),
% 2.03/0.65    inference(forward_demodulation,[],[f1219,f188])).
% 2.03/0.65  fof(f1219,plain,(
% 2.03/0.65    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,X0)) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,sK1),X0)))) )),
% 2.03/0.65    inference(backward_demodulation,[],[f904,f1186])).
% 2.03/0.65  fof(f904,plain,(
% 2.03/0.65    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,X0)) = k5_xboole_0(k5_xboole_0(k1_xboole_0,sK1),k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,k5_xboole_0(k1_xboole_0,sK1)),X0)))) )),
% 2.03/0.65    inference(forward_demodulation,[],[f902,f66])).
% 2.03/0.65  fof(f902,plain,(
% 2.03/0.65    ( ! [X0] : (k5_xboole_0(k5_xboole_0(k1_xboole_0,sK1),X0) = k5_xboole_0(k5_xboole_0(k1_xboole_0,sK1),k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,k5_xboole_0(k1_xboole_0,sK1)),X0)))) )),
% 2.03/0.65    inference(backward_demodulation,[],[f701,f899])).
% 2.03/0.65  fof(f701,plain,(
% 2.03/0.65    ( ! [X0] : (k5_xboole_0(k4_subset_1(sK0,k5_xboole_0(k1_xboole_0,sK1),sK1),X0) = k5_xboole_0(k5_xboole_0(k1_xboole_0,sK1),k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,k5_xboole_0(k1_xboole_0,sK1)),X0)))) )),
% 2.03/0.65    inference(forward_demodulation,[],[f700,f66])).
% 2.03/0.67  fof(f700,plain,(
% 2.03/0.67    ( ! [X0] : (k5_xboole_0(k5_xboole_0(k1_xboole_0,sK1),k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(k1_xboole_0,sK1))),X0)) = k5_xboole_0(k4_subset_1(sK0,k5_xboole_0(k1_xboole_0,sK1),sK1),X0)) )),
% 2.03/0.67    inference(superposition,[],[f66,f394])).
% 2.03/0.67  fof(f807,plain,(
% 2.03/0.67    ( ! [X0] : (k5_xboole_0(sK1,k5_xboole_0(sK1,X0)) = k5_xboole_0(k3_xboole_0(k1_xboole_0,sK1),X0)) )),
% 2.03/0.67    inference(superposition,[],[f66,f793])).
% 2.03/0.67  fof(f1657,plain,(
% 2.03/0.67    k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,k5_xboole_0(sK1,sK0))),
% 2.03/0.67    inference(superposition,[],[f1246,f1486])).
% 2.03/0.67  fof(f1486,plain,(
% 2.03/0.67    k5_xboole_0(sK0,sK1) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK0))),
% 2.03/0.67    inference(superposition,[],[f315,f1436])).
% 2.03/0.67  fof(f1436,plain,(
% 2.03/0.67    sK1 = k5_xboole_0(sK0,k5_xboole_0(sK1,sK0))),
% 2.03/0.67    inference(superposition,[],[f1402,f66])).
% 2.03/0.67  fof(f1402,plain,(
% 2.03/0.67    sK1 = k5_xboole_0(k5_xboole_0(sK0,sK1),sK0)),
% 2.03/0.67    inference(backward_demodulation,[],[f1374,f1388])).
% 2.03/0.67  fof(f1388,plain,(
% 2.03/0.67    sK1 = k3_xboole_0(sK1,sK1)),
% 2.03/0.67    inference(forward_demodulation,[],[f1387,f1186])).
% 2.03/0.67  fof(f1387,plain,(
% 2.03/0.67    k3_xboole_0(sK1,sK1) = k5_xboole_0(k1_xboole_0,sK1)),
% 2.03/0.67    inference(forward_demodulation,[],[f1386,f1374])).
% 2.03/0.67  fof(f1386,plain,(
% 2.03/0.67    k5_xboole_0(k1_xboole_0,sK1) = k5_xboole_0(k5_xboole_0(sK0,sK1),sK0)),
% 2.03/0.67    inference(forward_demodulation,[],[f1363,f43])).
% 2.03/0.67  fof(f1363,plain,(
% 2.03/0.67    k5_xboole_0(k1_xboole_0,sK1) = k5_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK0,k1_xboole_0))),
% 2.03/0.67    inference(superposition,[],[f918,f1273])).
% 2.03/0.67  fof(f1273,plain,(
% 2.03/0.67    k1_xboole_0 = k5_xboole_0(sK1,sK1)),
% 2.03/0.67    inference(backward_demodulation,[],[f793,f1272])).
% 2.03/0.67  fof(f918,plain,(
% 2.03/0.67    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,X0)))) )),
% 2.03/0.67    inference(forward_demodulation,[],[f917,f314])).
% 2.03/0.67  fof(f917,plain,(
% 2.03/0.67    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(k3_xboole_0(sK0,sK0),k5_xboole_0(sK1,X0)))) )),
% 2.03/0.67    inference(forward_demodulation,[],[f916,f312])).
% 2.03/0.67  fof(f312,plain,(
% 2.03/0.67    ( ! [X0,X1] : (k5_xboole_0(k3_xboole_0(X0,sK0),k5_xboole_0(sK1,X1)) = k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(X0,sK1)),X1)) )),
% 2.03/0.67    inference(superposition,[],[f66,f124])).
% 2.03/0.67  fof(f916,plain,(
% 2.03/0.67    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),X0))) )),
% 2.03/0.67    inference(forward_demodulation,[],[f909,f44])).
% 2.03/0.67  fof(f909,plain,(
% 2.03/0.67    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(k3_xboole_0(k5_xboole_0(sK0,sK1),sK0),X0))) )),
% 2.03/0.67    inference(backward_demodulation,[],[f625,f905])).
% 2.03/0.67  fof(f905,plain,(
% 2.03/0.67    sK0 = k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1)),
% 2.03/0.67    inference(forward_demodulation,[],[f897,f43])).
% 2.03/0.67  fof(f897,plain,(
% 2.03/0.67    k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(sK0,k1_xboole_0)),
% 2.03/0.67    inference(backward_demodulation,[],[f888,f870])).
% 2.03/0.67  fof(f888,plain,(
% 2.03/0.67    k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)))),
% 2.03/0.67    inference(forward_demodulation,[],[f887,f380])).
% 2.03/0.67  fof(f887,plain,(
% 2.03/0.67    k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(k1_xboole_0,k5_xboole_0(sK0,sK1))))),
% 2.03/0.67    inference(forward_demodulation,[],[f886,f315])).
% 2.03/0.67  fof(f886,plain,(
% 2.03/0.67    k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)))))),
% 2.03/0.67    inference(forward_demodulation,[],[f874,f867])).
% 2.03/0.67  fof(f874,plain,(
% 2.03/0.67    k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)))))),
% 2.03/0.67    inference(backward_demodulation,[],[f658,f867])).
% 2.03/0.67  fof(f658,plain,(
% 2.03/0.67    k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)))))),
% 2.03/0.67    inference(superposition,[],[f287,f66])).
% 2.03/0.67  fof(f287,plain,(
% 2.03/0.67    k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))))),
% 2.03/0.67    inference(superposition,[],[f117,f73])).
% 2.03/0.67  fof(f117,plain,(
% 2.03/0.67    k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1) = k3_tarski(k2_enumset1(k5_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1),sK1))),
% 2.03/0.67    inference(backward_demodulation,[],[f96,f114])).
% 2.03/0.67  fof(f96,plain,(
% 2.03/0.67    k4_subset_1(sK0,k3_subset_1(sK0,sK1),sK1) = k3_tarski(k2_enumset1(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1),sK1))),
% 2.03/0.67    inference(unit_resulting_resolution,[],[f39,f84,f75])).
% 2.03/0.67  fof(f625,plain,(
% 2.03/0.67    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(k3_xboole_0(k5_xboole_0(sK0,sK1),k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1)),X0))) )),
% 2.03/0.67    inference(superposition,[],[f66,f289])).
% 2.03/0.67  fof(f289,plain,(
% 2.03/0.67    k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(k5_xboole_0(sK0,sK1),k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1)))),
% 2.03/0.67    inference(superposition,[],[f71,f117])).
% 2.03/0.67  fof(f1374,plain,(
% 2.03/0.67    k3_xboole_0(sK1,sK1) = k5_xboole_0(k5_xboole_0(sK0,sK1),sK0)),
% 2.03/0.67    inference(forward_demodulation,[],[f1373,f1186])).
% 2.03/0.67  fof(f1373,plain,(
% 2.03/0.67    k3_xboole_0(sK1,k5_xboole_0(k1_xboole_0,sK1)) = k5_xboole_0(k5_xboole_0(sK0,sK1),sK0)),
% 2.03/0.67    inference(forward_demodulation,[],[f1372,f1312])).
% 2.03/0.67  fof(f1312,plain,(
% 2.03/0.67    ( ! [X1] : (k3_xboole_0(sK1,k5_xboole_0(k1_xboole_0,X1)) = k5_xboole_0(k1_xboole_0,k3_xboole_0(X1,sK1))) )),
% 2.03/0.67    inference(forward_demodulation,[],[f1304,f44])).
% 2.03/0.67  fof(f1304,plain,(
% 2.03/0.67    ( ! [X1] : (k3_xboole_0(k5_xboole_0(k1_xboole_0,X1),sK1) = k5_xboole_0(k1_xboole_0,k3_xboole_0(X1,sK1))) )),
% 2.03/0.67    inference(superposition,[],[f67,f1272])).
% 2.03/0.67  fof(f1372,plain,(
% 2.03/0.67    k5_xboole_0(k1_xboole_0,k3_xboole_0(sK1,sK1)) = k5_xboole_0(k5_xboole_0(sK0,sK1),sK0)),
% 2.03/0.67    inference(forward_demodulation,[],[f1355,f43])).
% 2.03/0.67  fof(f1355,plain,(
% 2.03/0.67    k5_xboole_0(k1_xboole_0,k3_xboole_0(sK1,sK1)) = k5_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK0,k1_xboole_0))),
% 2.03/0.67    inference(superposition,[],[f918,f186])).
% 2.03/0.67  fof(f1715,plain,(
% 2.03/0.67    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))),
% 2.03/0.67    inference(forward_demodulation,[],[f1714,f1388])).
% 2.03/0.67  fof(f1714,plain,(
% 2.03/0.67    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,k5_xboole_0(sK0,k3_xboole_0(sK1,sK1)))),
% 2.03/0.67    inference(forward_demodulation,[],[f1713,f1020])).
% 2.03/0.67  fof(f1020,plain,(
% 2.03/0.67    ( ! [X1] : (k5_xboole_0(sK0,k3_xboole_0(X1,sK1)) = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(k1_xboole_0,X1)))) )),
% 2.03/0.67    inference(forward_demodulation,[],[f1019,f315])).
% 2.03/0.67  fof(f1019,plain,(
% 2.03/0.67    ( ! [X1] : (k5_xboole_0(sK0,k3_xboole_0(X1,sK1)) = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK0,X1))))) )),
% 2.03/0.67    inference(forward_demodulation,[],[f1006,f867])).
% 2.03/0.67  fof(f1006,plain,(
% 2.03/0.67    ( ! [X1] : (k5_xboole_0(sK0,k3_xboole_0(X1,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK0,X1))))) )),
% 2.03/0.67    inference(superposition,[],[f163,f132])).
% 2.03/0.67  fof(f163,plain,(
% 2.03/0.67    ( ! [X0] : (k5_xboole_0(sK0,X0) = k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,X0)))) )),
% 2.03/0.67    inference(forward_demodulation,[],[f162,f66])).
% 2.03/0.67  fof(f162,plain,(
% 2.03/0.67    ( ! [X0] : (k5_xboole_0(sK0,X0) = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,sK1),X0))) )),
% 2.03/0.67    inference(superposition,[],[f66,f133])).
% 2.03/0.67  fof(f1713,plain,(
% 2.03/0.67    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(k1_xboole_0,sK1))))),
% 2.03/0.67    inference(forward_demodulation,[],[f1712,f315])).
% 2.03/0.67  fof(f1712,plain,(
% 2.03/0.67    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)))))),
% 2.03/0.67    inference(forward_demodulation,[],[f1711,f132])).
% 2.03/0.67  fof(f1711,plain,(
% 2.03/0.67    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK0,sK1),sK1))))),
% 2.03/0.67    inference(forward_demodulation,[],[f1710,f1189])).
% 2.03/0.67  fof(f1189,plain,(
% 2.03/0.67    sK1 = k3_subset_1(sK0,k5_xboole_0(sK0,sK1))),
% 2.03/0.67    inference(backward_demodulation,[],[f317,f1186])).
% 2.03/0.67  fof(f1710,plain,(
% 2.03/0.67    k4_subset_1(sK0,k3_subset_1(sK0,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK0,sK1)) = k5_xboole_0(k3_subset_1(sK0,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK0,sK1),k3_subset_1(sK0,k5_xboole_0(sK0,sK1))))))),
% 2.03/0.67    inference(forward_demodulation,[],[f1697,f114])).
% 2.03/0.67  fof(f1697,plain,(
% 2.03/0.67    k4_subset_1(sK0,k3_subset_1(sK0,k3_subset_1(sK0,sK1)),k5_xboole_0(sK0,sK1)) = k5_xboole_0(k3_subset_1(sK0,k3_subset_1(sK0,sK1)),k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK0,sK1),k3_subset_1(sK0,k3_subset_1(sK0,sK1))))))),
% 2.03/0.67    inference(unit_resulting_resolution,[],[f39,f836])).
% 2.03/0.67  fof(f836,plain,(
% 2.03/0.67    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(sK0)) | k4_subset_1(sK0,k3_subset_1(sK0,k3_subset_1(sK0,X1)),k5_xboole_0(sK0,sK1)) = k5_xboole_0(k3_subset_1(sK0,k3_subset_1(sK0,X1)),k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK0,sK1),k3_subset_1(sK0,k3_subset_1(sK0,X1))))))) )),
% 2.03/0.67    inference(forward_demodulation,[],[f835,f66])).
% 2.03/0.67  fof(f835,plain,(
% 2.03/0.67    ( ! [X1] : (k4_subset_1(sK0,k3_subset_1(sK0,k3_subset_1(sK0,X1)),k5_xboole_0(sK0,sK1)) = k5_xboole_0(k3_subset_1(sK0,k3_subset_1(sK0,X1)),k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(k5_xboole_0(sK0,sK1),k3_subset_1(sK0,k3_subset_1(sK0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(sK0))) )),
% 2.03/0.67    inference(forward_demodulation,[],[f824,f73])).
% 2.03/0.67  fof(f824,plain,(
% 2.03/0.67    ( ! [X1] : (k4_subset_1(sK0,k3_subset_1(sK0,k3_subset_1(sK0,X1)),k5_xboole_0(sK0,sK1)) = k3_tarski(k2_enumset1(k3_subset_1(sK0,k3_subset_1(sK0,X1)),k3_subset_1(sK0,k3_subset_1(sK0,X1)),k3_subset_1(sK0,k3_subset_1(sK0,X1)),k5_xboole_0(sK0,sK1))) | ~m1_subset_1(X1,k1_zfmisc_1(sK0))) )),
% 2.03/0.67    inference(resolution,[],[f302,f56])).
% 2.03/0.67  fof(f302,plain,(
% 2.03/0.67    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(sK0)) | k4_subset_1(sK0,k3_subset_1(sK0,X1),k5_xboole_0(sK0,sK1)) = k3_tarski(k2_enumset1(k3_subset_1(sK0,X1),k3_subset_1(sK0,X1),k3_subset_1(sK0,X1),k5_xboole_0(sK0,sK1)))) )),
% 2.03/0.67    inference(resolution,[],[f123,f56])).
% 2.03/0.67  fof(f123,plain,(
% 2.03/0.67    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | k4_subset_1(sK0,X0,k5_xboole_0(sK0,sK1)) = k3_tarski(k2_enumset1(X0,X0,X0,k5_xboole_0(sK0,sK1)))) )),
% 2.03/0.67    inference(backward_demodulation,[],[f103,f114])).
% 2.03/0.67  fof(f103,plain,(
% 2.03/0.67    ( ! [X0] : (k4_subset_1(sK0,X0,k3_subset_1(sK0,sK1)) = k3_tarski(k2_enumset1(X0,X0,X0,k3_subset_1(sK0,sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(sK0))) )),
% 2.03/0.67    inference(resolution,[],[f84,f75])).
% 2.03/0.67  % SZS output end Proof for theBenchmark
% 2.03/0.67  % (30377)------------------------------
% 2.03/0.67  % (30377)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.03/0.67  % (30377)Termination reason: Refutation
% 2.03/0.67  
% 2.03/0.67  % (30377)Memory used [KB]: 7164
% 2.03/0.67  % (30377)Time elapsed: 0.239 s
% 2.03/0.67  % (30377)------------------------------
% 2.03/0.67  % (30377)------------------------------
% 2.03/0.67  % (30364)Success in time 0.306 s
%------------------------------------------------------------------------------
