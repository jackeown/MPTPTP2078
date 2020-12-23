%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:46 EST 2020

% Result     : Theorem 2.08s
% Output     : Refutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 325 expanded)
%              Number of leaves         :   22 (  93 expanded)
%              Depth                    :   17
%              Number of atoms          :  132 ( 597 expanded)
%              Number of equality atoms :   68 ( 276 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f400,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f140,f390,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f49,f68])).

fof(f68,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f36,f64])).

fof(f64,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f41,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f53,f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f55,f61])).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f56,f60])).

fof(f60,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f57,f58])).

fof(f58,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f57,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f56,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f55,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f53,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f41,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f36,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f390,plain,(
    ! [X0] : ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f142,f360,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f38,f37])).

fof(f37,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f38,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f360,plain,(
    ! [X1] : k1_xboole_0 != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(forward_demodulation,[],[f356,f34])).

fof(f34,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f356,plain,(
    ! [X1] : k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ),
    inference(backward_demodulation,[],[f76,f353])).

fof(f353,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f339,f35])).

fof(f35,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f339,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f188,f34])).

fof(f188,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f54,f34])).

fof(f54,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f76,plain,(
    ! [X1] : k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k1_xboole_0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) ),
    inference(forward_demodulation,[],[f75,f34])).

fof(f75,plain,(
    ! [X1] : k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) ),
    inference(forward_demodulation,[],[f74,f69])).

fof(f69,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X4,X4,X4,X4,X4,X5,X6,X7))) ),
    inference(definition_unfolding,[],[f59,f65,f62,f62])).

fof(f65,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f40,f64])).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f59,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l75_enumset1)).

fof(f74,plain,(
    ! [X1] : k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) ) ),
    inference(definition_unfolding,[],[f52,f68,f67,f68,f68])).

fof(f67,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f42,f66])).

fof(f66,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f43,f65])).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f42,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f142,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f117,f122])).

fof(f122,plain,(
    k1_xboole_0 = sK0 ),
    inference(unit_resulting_resolution,[],[f117,f37])).

fof(f117,plain,(
    v1_xboole_0(sK0) ),
    inference(unit_resulting_resolution,[],[f86,f113,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f113,plain,(
    r2_hidden(sK2(sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f85,f32,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f32,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r2_hidden(X2,X1)
          | ~ m1_subset_1(X2,X0) )
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r2_hidden(X2,X1)
          | ~ m1_subset_1(X2,X0) )
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ~ ( ! [X2] :
                ( m1_subset_1(X2,X0)
               => ~ r2_hidden(X2,X1) )
            & k1_xboole_0 != X1 ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ~ ( ! [X2] :
              ( m1_subset_1(X2,X0)
             => ~ r2_hidden(X2,X1) )
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_subset_1)).

fof(f85,plain,(
    r2_hidden(sK2(sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f33,f39])).

fof(f39,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f33,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f25])).

fof(f86,plain,(
    ~ m1_subset_1(sK2(sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f85,f31])).

fof(f31,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,sK0)
      | ~ r2_hidden(X2,sK1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f140,plain,(
    r2_hidden(sK2(sK1),k1_xboole_0) ),
    inference(backward_demodulation,[],[f113,f122])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:45:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.55  % (20468)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.55  % (20457)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.55  % (20460)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.55  % (20457)Refutation not found, incomplete strategy% (20457)------------------------------
% 0.20/0.55  % (20457)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (20451)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.56  % (20457)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (20457)Memory used [KB]: 10618
% 0.20/0.56  % (20457)Time elapsed: 0.121 s
% 0.20/0.56  % (20457)------------------------------
% 0.20/0.56  % (20457)------------------------------
% 0.20/0.57  % (20468)Refutation not found, incomplete strategy% (20468)------------------------------
% 0.20/0.57  % (20468)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (20476)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.57  % (20453)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.57  % (20450)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.58  % (20458)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.58  % (20464)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.58  % (20468)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.58  
% 0.20/0.58  % (20468)Memory used [KB]: 10874
% 0.20/0.58  % (20468)Time elapsed: 0.138 s
% 0.20/0.58  % (20468)------------------------------
% 0.20/0.58  % (20468)------------------------------
% 0.20/0.59  % (20448)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.59  % (20454)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.60  % (20474)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.60  % (20452)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.60  % (20450)Refutation not found, incomplete strategy% (20450)------------------------------
% 0.20/0.60  % (20450)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.60  % (20450)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.60  
% 0.20/0.60  % (20450)Memory used [KB]: 10746
% 0.20/0.60  % (20450)Time elapsed: 0.173 s
% 0.20/0.60  % (20450)------------------------------
% 0.20/0.60  % (20450)------------------------------
% 0.20/0.60  % (20456)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.60  % (20458)Refutation not found, incomplete strategy% (20458)------------------------------
% 0.20/0.60  % (20458)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.60  % (20458)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.60  
% 0.20/0.60  % (20458)Memory used [KB]: 10618
% 0.20/0.60  % (20458)Time elapsed: 0.169 s
% 0.20/0.60  % (20458)------------------------------
% 0.20/0.60  % (20458)------------------------------
% 0.20/0.60  % (20456)Refutation not found, incomplete strategy% (20456)------------------------------
% 0.20/0.60  % (20456)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.60  % (20456)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.60  
% 0.20/0.60  % (20456)Memory used [KB]: 10746
% 0.20/0.60  % (20456)Time elapsed: 0.169 s
% 0.20/0.60  % (20456)------------------------------
% 0.20/0.60  % (20456)------------------------------
% 0.20/0.60  % (20471)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.60  % (20473)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.60  % (20472)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.60  % (20475)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.61  % (20452)Refutation not found, incomplete strategy% (20452)------------------------------
% 0.20/0.61  % (20452)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.61  % (20463)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.61  % (20466)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.61  % (20469)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.61  % (20462)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.61  % (20465)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.61  % (20465)Refutation not found, incomplete strategy% (20465)------------------------------
% 0.20/0.61  % (20465)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.61  % (20452)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.61  
% 0.20/0.61  % (20452)Memory used [KB]: 6268
% 0.20/0.61  % (20452)Time elapsed: 0.174 s
% 0.20/0.61  % (20452)------------------------------
% 0.20/0.61  % (20452)------------------------------
% 0.20/0.61  % (20449)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.61  % (20465)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.61  
% 0.20/0.61  % (20465)Memory used [KB]: 10618
% 0.20/0.61  % (20465)Time elapsed: 0.183 s
% 0.20/0.61  % (20465)------------------------------
% 0.20/0.61  % (20465)------------------------------
% 0.20/0.61  % (20461)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.62  % (20459)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.62  % (20455)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.62  % (20470)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.63  % (20470)Refutation not found, incomplete strategy% (20470)------------------------------
% 0.20/0.63  % (20470)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.63  % (20470)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.63  
% 0.20/0.63  % (20470)Memory used [KB]: 10746
% 0.20/0.63  % (20470)Time elapsed: 0.152 s
% 0.20/0.63  % (20470)------------------------------
% 0.20/0.63  % (20470)------------------------------
% 0.20/0.63  % (20469)Refutation not found, incomplete strategy% (20469)------------------------------
% 0.20/0.63  % (20469)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.63  % (20469)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.63  
% 0.20/0.63  % (20469)Memory used [KB]: 1791
% 0.20/0.63  % (20469)Time elapsed: 0.180 s
% 0.20/0.63  % (20469)------------------------------
% 0.20/0.63  % (20469)------------------------------
% 0.20/0.64  % (20467)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.64  % (20459)Refutation not found, incomplete strategy% (20459)------------------------------
% 0.20/0.64  % (20459)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.64  % (20459)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.64  
% 0.20/0.64  % (20459)Memory used [KB]: 10618
% 0.20/0.64  % (20459)Time elapsed: 0.210 s
% 0.20/0.64  % (20459)------------------------------
% 0.20/0.64  % (20459)------------------------------
% 0.20/0.64  % (20477)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 2.08/0.66  % (20472)Refutation found. Thanks to Tanya!
% 2.08/0.66  % SZS status Theorem for theBenchmark
% 2.08/0.66  % SZS output start Proof for theBenchmark
% 2.08/0.66  fof(f400,plain,(
% 2.08/0.66    $false),
% 2.08/0.66    inference(unit_resulting_resolution,[],[f140,f390,f71])).
% 2.08/0.66  fof(f71,plain,(
% 2.08/0.66    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.08/0.66    inference(definition_unfolding,[],[f49,f68])).
% 2.08/0.66  fof(f68,plain,(
% 2.08/0.66    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.08/0.66    inference(definition_unfolding,[],[f36,f64])).
% 2.08/0.66  fof(f64,plain,(
% 2.08/0.66    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.08/0.66    inference(definition_unfolding,[],[f41,f63])).
% 2.08/0.66  fof(f63,plain,(
% 2.08/0.66    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.08/0.66    inference(definition_unfolding,[],[f53,f62])).
% 2.08/0.66  fof(f62,plain,(
% 2.08/0.66    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.08/0.66    inference(definition_unfolding,[],[f55,f61])).
% 2.08/0.66  fof(f61,plain,(
% 2.08/0.66    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.08/0.66    inference(definition_unfolding,[],[f56,f60])).
% 2.08/0.66  fof(f60,plain,(
% 2.08/0.66    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.08/0.66    inference(definition_unfolding,[],[f57,f58])).
% 2.08/0.66  fof(f58,plain,(
% 2.08/0.66    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 2.08/0.66    inference(cnf_transformation,[],[f16])).
% 2.08/0.66  fof(f16,axiom,(
% 2.08/0.66    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 2.08/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 2.08/0.66  fof(f57,plain,(
% 2.08/0.66    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 2.08/0.66    inference(cnf_transformation,[],[f15])).
% 2.08/0.66  fof(f15,axiom,(
% 2.08/0.66    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 2.08/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 2.08/0.66  fof(f56,plain,(
% 2.08/0.66    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.08/0.66    inference(cnf_transformation,[],[f14])).
% 2.08/0.66  fof(f14,axiom,(
% 2.08/0.66    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.08/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 2.08/0.66  fof(f55,plain,(
% 2.08/0.66    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.08/0.66    inference(cnf_transformation,[],[f13])).
% 2.08/0.66  fof(f13,axiom,(
% 2.08/0.66    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.08/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 2.08/0.66  fof(f53,plain,(
% 2.08/0.66    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.08/0.66    inference(cnf_transformation,[],[f12])).
% 2.08/0.66  fof(f12,axiom,(
% 2.08/0.66    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.08/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 2.08/0.66  fof(f41,plain,(
% 2.08/0.66    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.08/0.66    inference(cnf_transformation,[],[f11])).
% 2.08/0.66  fof(f11,axiom,(
% 2.08/0.66    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.08/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 2.08/0.66  fof(f36,plain,(
% 2.08/0.66    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.08/0.66    inference(cnf_transformation,[],[f10])).
% 2.08/0.66  fof(f10,axiom,(
% 2.08/0.66    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.08/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 2.08/0.66  fof(f49,plain,(
% 2.08/0.66    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 2.08/0.66    inference(cnf_transformation,[],[f17])).
% 2.08/0.66  fof(f17,axiom,(
% 2.08/0.66    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 2.08/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 2.08/0.66  fof(f390,plain,(
% 2.08/0.66    ( ! [X0] : (~r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_xboole_0)) )),
% 2.08/0.66    inference(unit_resulting_resolution,[],[f142,f360,f83])).
% 2.08/0.66  fof(f83,plain,(
% 2.08/0.66    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 2.08/0.66    inference(superposition,[],[f38,f37])).
% 2.08/0.66  fof(f37,plain,(
% 2.08/0.66    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.08/0.66    inference(cnf_transformation,[],[f26])).
% 2.08/0.66  fof(f26,plain,(
% 2.08/0.66    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.08/0.66    inference(ennf_transformation,[],[f1])).
% 2.08/0.66  fof(f1,axiom,(
% 2.08/0.66    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.08/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 2.08/0.66  fof(f38,plain,(
% 2.08/0.66    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 2.08/0.66    inference(cnf_transformation,[],[f27])).
% 2.08/0.66  fof(f27,plain,(
% 2.08/0.66    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 2.08/0.66    inference(ennf_transformation,[],[f4])).
% 2.08/0.66  fof(f4,axiom,(
% 2.08/0.66    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 2.08/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 2.08/0.66  fof(f360,plain,(
% 2.08/0.66    ( ! [X1] : (k1_xboole_0 != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) )),
% 2.08/0.66    inference(forward_demodulation,[],[f356,f34])).
% 2.08/0.66  fof(f34,plain,(
% 2.08/0.66    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.08/0.66    inference(cnf_transformation,[],[f7])).
% 2.08/0.66  fof(f7,axiom,(
% 2.08/0.66    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 2.08/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 2.08/0.66  fof(f356,plain,(
% 2.08/0.66    ( ! [X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 2.08/0.66    inference(backward_demodulation,[],[f76,f353])).
% 2.08/0.66  fof(f353,plain,(
% 2.08/0.66    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 2.08/0.66    inference(forward_demodulation,[],[f339,f35])).
% 2.08/0.66  fof(f35,plain,(
% 2.08/0.66    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.08/0.66    inference(cnf_transformation,[],[f5])).
% 2.08/0.66  fof(f5,axiom,(
% 2.08/0.66    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.08/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 2.08/0.66  fof(f339,plain,(
% 2.08/0.66    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 2.08/0.66    inference(superposition,[],[f188,f34])).
% 2.08/0.66  fof(f188,plain,(
% 2.08/0.66    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)) )),
% 2.08/0.66    inference(superposition,[],[f54,f34])).
% 2.08/0.66  fof(f54,plain,(
% 2.08/0.66    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.08/0.66    inference(cnf_transformation,[],[f6])).
% 2.08/0.66  fof(f6,axiom,(
% 2.08/0.66    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.08/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.08/0.66  fof(f76,plain,(
% 2.08/0.66    ( ! [X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k1_xboole_0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) )),
% 2.08/0.66    inference(forward_demodulation,[],[f75,f34])).
% 2.08/0.66  fof(f75,plain,(
% 2.08/0.66    ( ! [X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) )),
% 2.08/0.66    inference(forward_demodulation,[],[f74,f69])).
% 2.08/0.66  fof(f69,plain,(
% 2.08/0.66    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3),k6_enumset1(X4,X4,X4,X4,X4,X5,X6,X7)))) )),
% 2.08/0.66    inference(definition_unfolding,[],[f59,f65,f62,f62])).
% 2.08/0.66  fof(f65,plain,(
% 2.08/0.66    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.08/0.66    inference(definition_unfolding,[],[f40,f64])).
% 2.08/0.66  fof(f40,plain,(
% 2.08/0.66    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.08/0.66    inference(cnf_transformation,[],[f18])).
% 2.08/0.66  fof(f18,axiom,(
% 2.08/0.66    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.08/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.08/0.66  fof(f59,plain,(
% 2.08/0.66    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))) )),
% 2.08/0.66    inference(cnf_transformation,[],[f9])).
% 2.08/0.66  fof(f9,axiom,(
% 2.08/0.66    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))),
% 2.08/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l75_enumset1)).
% 2.08/0.66  fof(f74,plain,(
% 2.08/0.66    ( ! [X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))))) )),
% 2.08/0.66    inference(equality_resolution,[],[f72])).
% 2.08/0.66  fof(f72,plain,(
% 2.08/0.66    ( ! [X0,X1] : (X0 != X1 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))))) )),
% 2.08/0.66    inference(definition_unfolding,[],[f52,f68,f67,f68,f68])).
% 2.08/0.66  fof(f67,plain,(
% 2.08/0.66    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 2.08/0.66    inference(definition_unfolding,[],[f42,f66])).
% 2.08/0.66  fof(f66,plain,(
% 2.08/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.08/0.66    inference(definition_unfolding,[],[f43,f65])).
% 2.08/0.66  fof(f43,plain,(
% 2.08/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 2.08/0.66    inference(cnf_transformation,[],[f8])).
% 2.08/0.66  fof(f8,axiom,(
% 2.08/0.66    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 2.08/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 2.08/0.66  fof(f42,plain,(
% 2.08/0.66    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.08/0.66    inference(cnf_transformation,[],[f3])).
% 2.08/0.66  fof(f3,axiom,(
% 2.08/0.66    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.08/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.08/0.66  fof(f52,plain,(
% 2.08/0.66    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 2.08/0.66    inference(cnf_transformation,[],[f19])).
% 2.08/0.66  fof(f19,axiom,(
% 2.08/0.66    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 2.08/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 2.08/0.66  fof(f142,plain,(
% 2.08/0.66    v1_xboole_0(k1_xboole_0)),
% 2.08/0.66    inference(backward_demodulation,[],[f117,f122])).
% 2.08/0.66  fof(f122,plain,(
% 2.08/0.66    k1_xboole_0 = sK0),
% 2.08/0.66    inference(unit_resulting_resolution,[],[f117,f37])).
% 2.08/0.66  fof(f117,plain,(
% 2.08/0.66    v1_xboole_0(sK0)),
% 2.08/0.66    inference(unit_resulting_resolution,[],[f86,f113,f46])).
% 2.08/0.66  fof(f46,plain,(
% 2.08/0.66    ( ! [X0,X1] : (~r2_hidden(X1,X0) | v1_xboole_0(X0) | m1_subset_1(X1,X0)) )),
% 2.08/0.66    inference(cnf_transformation,[],[f29])).
% 2.08/0.66  fof(f29,plain,(
% 2.08/0.66    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.08/0.66    inference(ennf_transformation,[],[f20])).
% 2.08/0.66  fof(f20,axiom,(
% 2.08/0.66    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.08/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 2.08/0.66  fof(f113,plain,(
% 2.08/0.66    r2_hidden(sK2(sK1),sK0)),
% 2.08/0.66    inference(unit_resulting_resolution,[],[f85,f32,f48])).
% 2.08/0.66  fof(f48,plain,(
% 2.08/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 2.08/0.66    inference(cnf_transformation,[],[f30])).
% 2.08/0.66  fof(f30,plain,(
% 2.08/0.66    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.08/0.66    inference(ennf_transformation,[],[f21])).
% 2.08/0.66  fof(f21,axiom,(
% 2.08/0.66    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 2.08/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 2.08/0.66  fof(f32,plain,(
% 2.08/0.66    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 2.08/0.66    inference(cnf_transformation,[],[f25])).
% 2.08/0.66  fof(f25,plain,(
% 2.08/0.66    ? [X0,X1] : (! [X2] : (~r2_hidden(X2,X1) | ~m1_subset_1(X2,X0)) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.08/0.66    inference(flattening,[],[f24])).
% 2.08/0.66  fof(f24,plain,(
% 2.08/0.66    ? [X0,X1] : ((! [X2] : (~r2_hidden(X2,X1) | ~m1_subset_1(X2,X0)) & k1_xboole_0 != X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.08/0.66    inference(ennf_transformation,[],[f23])).
% 2.08/0.66  fof(f23,negated_conjecture,(
% 2.08/0.66    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~(! [X2] : (m1_subset_1(X2,X0) => ~r2_hidden(X2,X1)) & k1_xboole_0 != X1))),
% 2.08/0.66    inference(negated_conjecture,[],[f22])).
% 2.08/0.66  fof(f22,conjecture,(
% 2.08/0.66    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~(! [X2] : (m1_subset_1(X2,X0) => ~r2_hidden(X2,X1)) & k1_xboole_0 != X1))),
% 2.08/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_subset_1)).
% 2.08/0.66  fof(f85,plain,(
% 2.08/0.66    r2_hidden(sK2(sK1),sK1)),
% 2.08/0.66    inference(unit_resulting_resolution,[],[f33,f39])).
% 2.08/0.66  fof(f39,plain,(
% 2.08/0.66    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 2.08/0.66    inference(cnf_transformation,[],[f28])).
% 2.08/0.66  fof(f28,plain,(
% 2.08/0.66    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.08/0.66    inference(ennf_transformation,[],[f2])).
% 2.08/0.66  fof(f2,axiom,(
% 2.08/0.66    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.08/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 2.08/0.66  fof(f33,plain,(
% 2.08/0.66    k1_xboole_0 != sK1),
% 2.08/0.66    inference(cnf_transformation,[],[f25])).
% 2.08/0.66  fof(f86,plain,(
% 2.08/0.66    ~m1_subset_1(sK2(sK1),sK0)),
% 2.08/0.66    inference(unit_resulting_resolution,[],[f85,f31])).
% 2.08/0.66  fof(f31,plain,(
% 2.08/0.66    ( ! [X2] : (~m1_subset_1(X2,sK0) | ~r2_hidden(X2,sK1)) )),
% 2.08/0.66    inference(cnf_transformation,[],[f25])).
% 2.08/0.66  fof(f140,plain,(
% 2.08/0.66    r2_hidden(sK2(sK1),k1_xboole_0)),
% 2.08/0.66    inference(backward_demodulation,[],[f113,f122])).
% 2.08/0.66  % SZS output end Proof for theBenchmark
% 2.08/0.66  % (20472)------------------------------
% 2.08/0.66  % (20472)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.08/0.66  % (20472)Termination reason: Refutation
% 2.08/0.66  
% 2.08/0.66  % (20472)Memory used [KB]: 6524
% 2.08/0.66  % (20472)Time elapsed: 0.234 s
% 2.08/0.66  % (20472)------------------------------
% 2.08/0.66  % (20472)------------------------------
% 2.08/0.66  % (20446)Success in time 0.295 s
%------------------------------------------------------------------------------
