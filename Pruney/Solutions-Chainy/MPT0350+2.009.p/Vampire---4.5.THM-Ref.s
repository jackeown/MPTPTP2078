%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:51 EST 2020

% Result     : Theorem 1.44s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 366 expanded)
%              Number of leaves         :   22 ( 112 expanded)
%              Depth                    :   18
%              Number of atoms          :  186 ( 674 expanded)
%              Number of equality atoms :   80 ( 319 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1151,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1150,f108])).

fof(f108,plain,(
    sK0 != k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f73,f100])).

fof(f100,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f39,f36])).

fof(f36,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f29])).

fof(f29,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f73,plain,(
    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f37,f41])).

fof(f41,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f37,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f1150,plain,(
    sK0 = k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1149,f189])).

fof(f189,plain,(
    ! [X2] : k4_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f187,f60])).

fof(f60,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f187,plain,(
    ! [X2] : k4_xboole_0(X2,k1_xboole_0) = k5_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[],[f65,f159])).

fof(f159,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f145,f84])).

fof(f84,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f82,f82])).

fof(f82,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(resolution,[],[f68,f56])).

fof(f56,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f55,f54])).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f145,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f69,f134])).

fof(f134,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f130,f60])).

fof(f130,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f65,f82])).

fof(f69,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f57,f54,f54])).

fof(f57,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f65,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f53,f54])).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f1149,plain,(
    k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f1148,f190])).

fof(f190,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f159,f189])).

fof(f1148,plain,(
    k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,k4_xboole_0(sK1,sK1)) ),
    inference(backward_demodulation,[],[f944,f1147])).

fof(f1147,plain,(
    ! [X8] : k4_xboole_0(sK0,k4_xboole_0(X8,sK1)) = k3_tarski(k2_enumset1(sK1,sK1,sK1,k4_xboole_0(sK0,X8))) ),
    inference(forward_demodulation,[],[f1110,f70])).

fof(f70,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f59,f63,f63])).

fof(f63,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f58,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f58,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f59,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f1110,plain,(
    ! [X8] : k4_xboole_0(sK0,k4_xboole_0(X8,sK1)) = k3_tarski(k2_enumset1(k4_xboole_0(sK0,X8),k4_xboole_0(sK0,X8),k4_xboole_0(sK0,X8),sK1)) ),
    inference(superposition,[],[f67,f162])).

fof(f162,plain,(
    sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f147,f137])).

fof(f137,plain,(
    sK1 = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f83,f136])).

fof(f136,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK0) ),
    inference(forward_demodulation,[],[f131,f61])).

fof(f61,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f131,plain,(
    k4_xboole_0(sK1,sK0) = k5_xboole_0(sK1,sK1) ),
    inference(superposition,[],[f65,f83])).

fof(f83,plain,(
    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) ),
    inference(resolution,[],[f68,f77])).

fof(f77,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f76,f72])).

fof(f72,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).

fof(f34,plain,(
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

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f76,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f75,f50])).

fof(f50,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f75,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f42,f36])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f147,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f69,f136])).

fof(f67,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k3_tarski(k2_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) ),
    inference(definition_unfolding,[],[f51,f64,f54])).

fof(f64,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f52,f63])).

fof(f52,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f51,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f944,plain,(
    k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k3_tarski(k2_enumset1(sK1,sK1,sK1,k4_xboole_0(sK0,sK1))) ),
    inference(resolution,[],[f940,f116])).

fof(f116,plain,(
    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f115,f36])).

fof(f115,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f40,f100])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f940,plain,(
    ! [X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(sK0))
      | k4_subset_1(sK0,sK1,X11) = k3_tarski(k2_enumset1(sK1,sK1,sK1,X11)) ) ),
    inference(resolution,[],[f66,f36])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k2_enumset1(X1,X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f38,f64])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:59:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (12956)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.49  % (12976)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.50  % (12968)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.50  % (12960)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.51  % (12959)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.51  % (12958)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.51  % (12957)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (12970)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.52  % (12972)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.52  % (12962)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.52  % (12973)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.52  % (12952)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.52  % (12978)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.52  % (12964)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (12971)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.52  % (12954)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (12965)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.52  % (12979)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.52  % (12955)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (12966)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (12974)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.53  % (12975)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.53  % (12963)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.53  % (12977)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.53  % (12981)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  % (12974)Refutation not found, incomplete strategy% (12974)------------------------------
% 0.22/0.54  % (12974)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (12953)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (12974)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (12974)Memory used [KB]: 10746
% 0.22/0.54  % (12974)Time elapsed: 0.126 s
% 0.22/0.54  % (12974)------------------------------
% 0.22/0.54  % (12974)------------------------------
% 0.22/0.54  % (12980)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (12961)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.54  % (12967)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.32/0.55  % (12969)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.32/0.56  % (12969)Refutation not found, incomplete strategy% (12969)------------------------------
% 1.32/0.56  % (12969)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.56  % (12969)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.56  
% 1.32/0.56  % (12969)Memory used [KB]: 10618
% 1.32/0.56  % (12969)Time elapsed: 0.123 s
% 1.32/0.56  % (12969)------------------------------
% 1.32/0.56  % (12969)------------------------------
% 1.44/0.57  % (12957)Refutation found. Thanks to Tanya!
% 1.44/0.57  % SZS status Theorem for theBenchmark
% 1.44/0.57  % SZS output start Proof for theBenchmark
% 1.44/0.57  fof(f1151,plain,(
% 1.44/0.57    $false),
% 1.44/0.57    inference(subsumption_resolution,[],[f1150,f108])).
% 1.44/0.57  fof(f108,plain,(
% 1.44/0.57    sK0 != k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1))),
% 1.44/0.57    inference(backward_demodulation,[],[f73,f100])).
% 1.44/0.57  fof(f100,plain,(
% 1.44/0.57    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 1.44/0.57    inference(resolution,[],[f39,f36])).
% 1.44/0.57  fof(f36,plain,(
% 1.44/0.57    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.44/0.57    inference(cnf_transformation,[],[f30])).
% 1.44/0.57  fof(f30,plain,(
% 1.44/0.57    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.44/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f29])).
% 1.44/0.57  fof(f29,plain,(
% 1.44/0.57    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.44/0.57    introduced(choice_axiom,[])).
% 1.44/0.57  fof(f22,plain,(
% 1.44/0.57    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.44/0.57    inference(ennf_transformation,[],[f21])).
% 1.44/0.57  fof(f21,negated_conjecture,(
% 1.44/0.57    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 1.44/0.57    inference(negated_conjecture,[],[f20])).
% 1.44/0.57  fof(f20,conjecture,(
% 1.44/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 1.44/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).
% 1.44/0.57  fof(f39,plain,(
% 1.44/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 1.44/0.57    inference(cnf_transformation,[],[f25])).
% 1.44/0.57  fof(f25,plain,(
% 1.44/0.57    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.44/0.57    inference(ennf_transformation,[],[f16])).
% 1.44/0.57  fof(f16,axiom,(
% 1.44/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.44/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.44/0.57  fof(f73,plain,(
% 1.44/0.57    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 1.44/0.57    inference(backward_demodulation,[],[f37,f41])).
% 1.44/0.57  fof(f41,plain,(
% 1.44/0.57    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.44/0.57    inference(cnf_transformation,[],[f15])).
% 1.44/0.57  fof(f15,axiom,(
% 1.44/0.57    ! [X0] : k2_subset_1(X0) = X0),
% 1.44/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 1.44/0.57  fof(f37,plain,(
% 1.44/0.57    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 1.44/0.57    inference(cnf_transformation,[],[f30])).
% 1.44/0.57  fof(f1150,plain,(
% 1.44/0.57    sK0 = k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1))),
% 1.44/0.57    inference(forward_demodulation,[],[f1149,f189])).
% 1.44/0.57  fof(f189,plain,(
% 1.44/0.57    ( ! [X2] : (k4_xboole_0(X2,k1_xboole_0) = X2) )),
% 1.44/0.57    inference(forward_demodulation,[],[f187,f60])).
% 1.44/0.57  fof(f60,plain,(
% 1.44/0.57    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.44/0.57    inference(cnf_transformation,[],[f7])).
% 1.44/0.57  fof(f7,axiom,(
% 1.44/0.57    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.44/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.44/0.57  fof(f187,plain,(
% 1.44/0.57    ( ! [X2] : (k4_xboole_0(X2,k1_xboole_0) = k5_xboole_0(X2,k1_xboole_0)) )),
% 1.44/0.57    inference(superposition,[],[f65,f159])).
% 1.44/0.57  fof(f159,plain,(
% 1.44/0.57    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 1.44/0.57    inference(forward_demodulation,[],[f145,f84])).
% 1.44/0.57  fof(f84,plain,(
% 1.44/0.57    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.44/0.57    inference(superposition,[],[f82,f82])).
% 1.44/0.57  fof(f82,plain,(
% 1.44/0.57    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) )),
% 1.44/0.57    inference(resolution,[],[f68,f56])).
% 1.44/0.57  fof(f56,plain,(
% 1.44/0.57    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.44/0.57    inference(cnf_transformation,[],[f4])).
% 1.44/0.57  fof(f4,axiom,(
% 1.44/0.57    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.44/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.44/0.57  fof(f68,plain,(
% 1.44/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 1.44/0.57    inference(definition_unfolding,[],[f55,f54])).
% 1.44/0.57  fof(f54,plain,(
% 1.44/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.44/0.57    inference(cnf_transformation,[],[f5])).
% 1.44/0.57  fof(f5,axiom,(
% 1.44/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.44/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.44/0.57  fof(f55,plain,(
% 1.44/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.44/0.57    inference(cnf_transformation,[],[f28])).
% 1.44/0.57  fof(f28,plain,(
% 1.44/0.57    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.44/0.57    inference(ennf_transformation,[],[f3])).
% 1.44/0.57  fof(f3,axiom,(
% 1.44/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.44/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.44/0.57  fof(f145,plain,(
% 1.44/0.57    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(k1_xboole_0,k1_xboole_0)) )),
% 1.44/0.57    inference(superposition,[],[f69,f134])).
% 1.44/0.57  fof(f134,plain,(
% 1.44/0.57    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.44/0.57    inference(forward_demodulation,[],[f130,f60])).
% 1.44/0.57  fof(f130,plain,(
% 1.44/0.57    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.44/0.57    inference(superposition,[],[f65,f82])).
% 1.44/0.57  fof(f69,plain,(
% 1.44/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.44/0.57    inference(definition_unfolding,[],[f57,f54,f54])).
% 1.44/0.57  fof(f57,plain,(
% 1.44/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.44/0.57    inference(cnf_transformation,[],[f1])).
% 1.44/0.57  fof(f1,axiom,(
% 1.44/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.44/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.44/0.57  fof(f65,plain,(
% 1.44/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.44/0.57    inference(definition_unfolding,[],[f53,f54])).
% 1.44/0.57  fof(f53,plain,(
% 1.44/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.44/0.57    inference(cnf_transformation,[],[f2])).
% 1.44/0.57  fof(f2,axiom,(
% 1.44/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.44/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.44/0.57  fof(f1149,plain,(
% 1.44/0.57    k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,k1_xboole_0)),
% 1.44/0.57    inference(forward_demodulation,[],[f1148,f190])).
% 1.44/0.57  fof(f190,plain,(
% 1.44/0.57    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.44/0.57    inference(backward_demodulation,[],[f159,f189])).
% 1.44/0.57  fof(f1148,plain,(
% 1.44/0.57    k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,k4_xboole_0(sK1,sK1))),
% 1.44/0.57    inference(backward_demodulation,[],[f944,f1147])).
% 1.44/0.57  fof(f1147,plain,(
% 1.44/0.57    ( ! [X8] : (k4_xboole_0(sK0,k4_xboole_0(X8,sK1)) = k3_tarski(k2_enumset1(sK1,sK1,sK1,k4_xboole_0(sK0,X8)))) )),
% 1.44/0.57    inference(forward_demodulation,[],[f1110,f70])).
% 1.44/0.57  fof(f70,plain,(
% 1.44/0.57    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 1.44/0.57    inference(definition_unfolding,[],[f59,f63,f63])).
% 1.44/0.57  fof(f63,plain,(
% 1.44/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.44/0.57    inference(definition_unfolding,[],[f58,f62])).
% 1.44/0.57  fof(f62,plain,(
% 1.44/0.57    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.44/0.57    inference(cnf_transformation,[],[f11])).
% 1.44/0.57  fof(f11,axiom,(
% 1.44/0.57    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.44/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.44/0.57  fof(f58,plain,(
% 1.44/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.44/0.57    inference(cnf_transformation,[],[f10])).
% 1.44/0.57  fof(f10,axiom,(
% 1.44/0.57    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.44/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.44/0.57  fof(f59,plain,(
% 1.44/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.44/0.57    inference(cnf_transformation,[],[f9])).
% 1.44/0.57  fof(f9,axiom,(
% 1.44/0.57    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.44/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.44/0.57  fof(f1110,plain,(
% 1.44/0.57    ( ! [X8] : (k4_xboole_0(sK0,k4_xboole_0(X8,sK1)) = k3_tarski(k2_enumset1(k4_xboole_0(sK0,X8),k4_xboole_0(sK0,X8),k4_xboole_0(sK0,X8),sK1))) )),
% 1.44/0.57    inference(superposition,[],[f67,f162])).
% 1.44/0.57  fof(f162,plain,(
% 1.44/0.57    sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 1.44/0.57    inference(forward_demodulation,[],[f147,f137])).
% 1.44/0.57  fof(f137,plain,(
% 1.44/0.57    sK1 = k4_xboole_0(sK1,k1_xboole_0)),
% 1.44/0.57    inference(backward_demodulation,[],[f83,f136])).
% 1.44/0.57  fof(f136,plain,(
% 1.44/0.57    k1_xboole_0 = k4_xboole_0(sK1,sK0)),
% 1.44/0.57    inference(forward_demodulation,[],[f131,f61])).
% 1.44/0.57  fof(f61,plain,(
% 1.44/0.57    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.44/0.57    inference(cnf_transformation,[],[f8])).
% 1.44/0.57  fof(f8,axiom,(
% 1.44/0.57    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.44/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.44/0.57  fof(f131,plain,(
% 1.44/0.57    k4_xboole_0(sK1,sK0) = k5_xboole_0(sK1,sK1)),
% 1.44/0.57    inference(superposition,[],[f65,f83])).
% 1.44/0.57  fof(f83,plain,(
% 1.44/0.57    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))),
% 1.44/0.57    inference(resolution,[],[f68,f77])).
% 1.44/0.57  fof(f77,plain,(
% 1.44/0.57    r1_tarski(sK1,sK0)),
% 1.44/0.57    inference(resolution,[],[f76,f72])).
% 1.44/0.57  fof(f72,plain,(
% 1.44/0.57    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 1.44/0.57    inference(equality_resolution,[],[f46])).
% 1.44/0.57  fof(f46,plain,(
% 1.44/0.57    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.44/0.57    inference(cnf_transformation,[],[f35])).
% 1.44/0.57  fof(f35,plain,(
% 1.44/0.57    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.44/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).
% 1.44/0.57  fof(f34,plain,(
% 1.44/0.57    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 1.44/0.57    introduced(choice_axiom,[])).
% 1.44/0.57  fof(f33,plain,(
% 1.44/0.57    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.44/0.57    inference(rectify,[],[f32])).
% 1.44/0.57  fof(f32,plain,(
% 1.44/0.57    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.44/0.57    inference(nnf_transformation,[],[f12])).
% 1.44/0.57  fof(f12,axiom,(
% 1.44/0.57    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.44/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.44/0.57  fof(f76,plain,(
% 1.44/0.57    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.44/0.57    inference(subsumption_resolution,[],[f75,f50])).
% 1.44/0.57  fof(f50,plain,(
% 1.44/0.57    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.44/0.57    inference(cnf_transformation,[],[f18])).
% 1.44/0.57  fof(f18,axiom,(
% 1.44/0.57    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.44/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.44/0.57  fof(f75,plain,(
% 1.44/0.57    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.44/0.57    inference(resolution,[],[f42,f36])).
% 1.44/0.57  fof(f42,plain,(
% 1.44/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.44/0.57    inference(cnf_transformation,[],[f31])).
% 1.44/0.57  fof(f31,plain,(
% 1.44/0.57    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.44/0.57    inference(nnf_transformation,[],[f27])).
% 1.44/0.57  fof(f27,plain,(
% 1.44/0.57    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.44/0.57    inference(ennf_transformation,[],[f14])).
% 1.44/0.57  fof(f14,axiom,(
% 1.44/0.57    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.44/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 1.44/0.57  fof(f147,plain,(
% 1.44/0.57    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK1,k1_xboole_0)),
% 1.44/0.57    inference(superposition,[],[f69,f136])).
% 1.44/0.57  fof(f67,plain,(
% 1.44/0.57    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k3_tarski(k2_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))))) )),
% 1.44/0.57    inference(definition_unfolding,[],[f51,f64,f54])).
% 1.44/0.57  fof(f64,plain,(
% 1.44/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 1.44/0.57    inference(definition_unfolding,[],[f52,f63])).
% 1.44/0.57  fof(f52,plain,(
% 1.44/0.57    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 1.44/0.57    inference(cnf_transformation,[],[f13])).
% 1.44/0.57  fof(f13,axiom,(
% 1.44/0.57    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 1.44/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.44/0.57  fof(f51,plain,(
% 1.44/0.57    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 1.44/0.57    inference(cnf_transformation,[],[f6])).
% 1.44/0.57  fof(f6,axiom,(
% 1.44/0.57    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 1.44/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).
% 1.44/0.57  fof(f944,plain,(
% 1.44/0.57    k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k3_tarski(k2_enumset1(sK1,sK1,sK1,k4_xboole_0(sK0,sK1)))),
% 1.44/0.57    inference(resolution,[],[f940,f116])).
% 1.44/0.57  fof(f116,plain,(
% 1.44/0.57    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 1.44/0.57    inference(subsumption_resolution,[],[f115,f36])).
% 1.44/0.57  fof(f115,plain,(
% 1.44/0.57    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.44/0.57    inference(superposition,[],[f40,f100])).
% 1.44/0.57  fof(f40,plain,(
% 1.44/0.57    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.44/0.57    inference(cnf_transformation,[],[f26])).
% 1.44/0.57  fof(f26,plain,(
% 1.44/0.57    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.44/0.57    inference(ennf_transformation,[],[f17])).
% 1.44/0.57  fof(f17,axiom,(
% 1.44/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.44/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 1.44/0.57  fof(f940,plain,(
% 1.44/0.57    ( ! [X11] : (~m1_subset_1(X11,k1_zfmisc_1(sK0)) | k4_subset_1(sK0,sK1,X11) = k3_tarski(k2_enumset1(sK1,sK1,sK1,X11))) )),
% 1.44/0.57    inference(resolution,[],[f66,f36])).
% 1.44/0.57  fof(f66,plain,(
% 1.44/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k2_enumset1(X1,X1,X1,X2))) )),
% 1.44/0.57    inference(definition_unfolding,[],[f38,f64])).
% 1.44/0.57  fof(f38,plain,(
% 1.44/0.57    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.44/0.57    inference(cnf_transformation,[],[f24])).
% 1.44/0.57  fof(f24,plain,(
% 1.44/0.57    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.44/0.57    inference(flattening,[],[f23])).
% 1.44/0.57  fof(f23,plain,(
% 1.44/0.57    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.44/0.57    inference(ennf_transformation,[],[f19])).
% 1.44/0.57  fof(f19,axiom,(
% 1.44/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 1.44/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.44/0.57  % SZS output end Proof for theBenchmark
% 1.44/0.57  % (12957)------------------------------
% 1.44/0.57  % (12957)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.57  % (12957)Termination reason: Refutation
% 1.44/0.57  
% 1.44/0.57  % (12957)Memory used [KB]: 6780
% 1.44/0.57  % (12957)Time elapsed: 0.145 s
% 1.44/0.57  % (12957)------------------------------
% 1.44/0.57  % (12957)------------------------------
% 1.44/0.59  % (12951)Success in time 0.218 s
%------------------------------------------------------------------------------
