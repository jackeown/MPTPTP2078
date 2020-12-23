%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:45 EST 2020

% Result     : Theorem 1.81s
% Output     : Refutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :  146 (3461 expanded)
%              Number of leaves         :   14 ( 921 expanded)
%              Depth                    :   36
%              Number of atoms          :  310 (8014 expanded)
%              Number of equality atoms :  105 (2425 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1057,plain,(
    $false ),
    inference(global_subsumption,[],[f95,f1056])).

fof(f1056,plain,(
    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f1037,f949])).

fof(f949,plain,(
    k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f939,f349])).

fof(f349,plain,(
    k1_xboole_0 = k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0)) ),
    inference(global_subsumption,[],[f32,f348])).

fof(f348,plain,
    ( k1_xboole_0 = k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f347,f36])).

fof(f36,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f347,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | k1_xboole_0 = k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0)) ),
    inference(duplicate_literal_removal,[],[f345])).

fof(f345,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | k1_xboole_0 = k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f218,f38])).

fof(f38,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f218,plain,
    ( ~ v1_relat_1(k4_relat_1(k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0)
    | k1_xboole_0 = k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f216,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f216,plain,
    ( v1_xboole_0(k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0)))
    | ~ v1_relat_1(k4_relat_1(k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f164,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f164,plain,
    ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0)))
    | v1_xboole_0(k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0))) ),
    inference(global_subsumption,[],[f32,f163])).

fof(f163,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0)))
    | v1_xboole_0(k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0))) ),
    inference(superposition,[],[f42,f158])).

fof(f158,plain,(
    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0))) ),
    inference(resolution,[],[f143,f32])).

fof(f143,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(X0))) ) ),
    inference(resolution,[],[f78,f36])).

fof(f78,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(X1))) ) ),
    inference(resolution,[],[f75,f38])).

fof(f75,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) ) ),
    inference(resolution,[],[f74,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f46,f35])).

fof(f35,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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

fof(f74,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(global_subsumption,[],[f32,f73])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0)
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[],[f72,f36])).

fof(f72,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X0)
      | r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) ) ),
    inference(superposition,[],[f40,f33])).

fof(f33,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).

fof(f32,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f939,plain,(
    k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0)) = k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0))) ),
    inference(resolution,[],[f698,f643])).

fof(f643,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f56,f642])).

fof(f642,plain,(
    v1_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(global_subsumption,[],[f32,f641])).

fof(f641,plain,
    ( v1_relat_1(k4_relat_1(k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f640,f636])).

fof(f636,plain,(
    k4_relat_1(k1_xboole_0) = k5_relat_1(sK0,k4_relat_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f633,f169])).

fof(f169,plain,(
    k1_xboole_0 = k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) ),
    inference(global_subsumption,[],[f32,f168])).

fof(f168,plain,
    ( k1_xboole_0 = k5_relat_1(k1_xboole_0,k4_relat_1(sK0))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f167,f36])).

fof(f167,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | k1_xboole_0 = k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) ),
    inference(global_subsumption,[],[f30,f165])).

fof(f165,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | k1_xboole_0 = k5_relat_1(k1_xboole_0,k4_relat_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f157,f38])).

fof(f157,plain,
    ( ~ v1_relat_1(k4_relat_1(sK0))
    | ~ v1_relat_1(k1_xboole_0)
    | k1_xboole_0 = k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) ),
    inference(resolution,[],[f152,f37])).

fof(f152,plain,
    ( v1_xboole_0(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))
    | ~ v1_relat_1(k4_relat_1(sK0))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f151,f43])).

fof(f151,plain,
    ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))
    | v1_xboole_0(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) ),
    inference(global_subsumption,[],[f32,f150])).

fof(f150,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))
    | v1_xboole_0(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) ),
    inference(superposition,[],[f42,f146])).

fof(f146,plain,(
    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) ),
    inference(resolution,[],[f78,f30])).

fof(f30,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

fof(f633,plain,(
    k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) = k5_relat_1(sK0,k4_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f618,f32])).

fof(f618,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k5_relat_1(sK0,k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,k4_relat_1(sK0))) ) ),
    inference(resolution,[],[f617,f36])).

fof(f617,plain,(
    ! [X12] :
      ( ~ v1_relat_1(X12)
      | k4_relat_1(k5_relat_1(X12,k4_relat_1(sK0))) = k5_relat_1(sK0,k4_relat_1(X12)) ) ),
    inference(forward_demodulation,[],[f612,f50])).

fof(f50,plain,(
    sK0 = k4_relat_1(k4_relat_1(sK0)) ),
    inference(resolution,[],[f39,f30])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

fof(f612,plain,(
    ! [X12] :
      ( ~ v1_relat_1(X12)
      | k4_relat_1(k5_relat_1(X12,k4_relat_1(sK0))) = k5_relat_1(k4_relat_1(k4_relat_1(sK0)),k4_relat_1(X12)) ) ),
    inference(resolution,[],[f117,f30])).

fof(f117,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2)
      | k4_relat_1(k5_relat_1(X2,k4_relat_1(X3))) = k5_relat_1(k4_relat_1(k4_relat_1(X3)),k4_relat_1(X2)) ) ),
    inference(resolution,[],[f41,f38])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

fof(f640,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_relat_1(k5_relat_1(sK0,k4_relat_1(k1_xboole_0))) ),
    inference(forward_demodulation,[],[f637,f55])).

fof(f55,plain,(
    k1_xboole_0 = k4_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f51,f32])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    inference(resolution,[],[f39,f36])).

fof(f637,plain,
    ( ~ v1_xboole_0(k4_relat_1(k4_relat_1(k1_xboole_0)))
    | v1_relat_1(k5_relat_1(sK0,k4_relat_1(k1_xboole_0))) ),
    inference(backward_demodulation,[],[f325,f636])).

fof(f325,plain,
    ( ~ v1_xboole_0(k4_relat_1(k5_relat_1(sK0,k4_relat_1(k1_xboole_0))))
    | v1_relat_1(k5_relat_1(sK0,k4_relat_1(k1_xboole_0))) ),
    inference(resolution,[],[f323,f36])).

fof(f323,plain,
    ( ~ v1_relat_1(k4_relat_1(k5_relat_1(sK0,k4_relat_1(k1_xboole_0))))
    | v1_relat_1(k5_relat_1(sK0,k4_relat_1(k1_xboole_0))) ),
    inference(superposition,[],[f38,f320])).

fof(f320,plain,(
    k5_relat_1(sK0,k4_relat_1(k1_xboole_0)) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k4_relat_1(k1_xboole_0)))) ),
    inference(resolution,[],[f310,f32])).

% (15345)Termination reason: Refutation not found, incomplete strategy
fof(f310,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k5_relat_1(sK0,k4_relat_1(X0)) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k4_relat_1(X0)))) ) ),
    inference(resolution,[],[f256,f36])).

fof(f256,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | k5_relat_1(sK0,k4_relat_1(X1)) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k4_relat_1(X1)))) ) ),
    inference(resolution,[],[f254,f38])).

fof(f254,plain,(
    ! [X8] :
      ( ~ v1_relat_1(X8)
      | k5_relat_1(sK0,X8) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,X8))) ) ),
    inference(resolution,[],[f59,f30])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k5_relat_1(X1,X0) = k4_relat_1(k4_relat_1(k5_relat_1(X1,X0))) ) ),
    inference(resolution,[],[f43,f39])).

fof(f56,plain,
    ( ~ v1_relat_1(k4_relat_1(k1_xboole_0))
    | v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f38,f55])).

fof(f698,plain,(
    ! [X4] :
      ( ~ v1_relat_1(X4)
      | k4_relat_1(k5_relat_1(X4,k4_relat_1(k1_xboole_0))) = k5_relat_1(k1_xboole_0,k4_relat_1(X4)) ) ),
    inference(forward_demodulation,[],[f684,f55])).

fof(f684,plain,(
    ! [X4] :
      ( ~ v1_relat_1(X4)
      | k4_relat_1(k5_relat_1(X4,k4_relat_1(k1_xboole_0))) = k5_relat_1(k4_relat_1(k4_relat_1(k1_xboole_0)),k4_relat_1(X4)) ) ),
    inference(resolution,[],[f643,f117])).

fof(f1037,plain,(
    k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f294,f1036])).

% (15345)Memory used [KB]: 6012
% (15345)Time elapsed: 0.200 s
% (15345)------------------------------
% (15345)------------------------------
fof(f1036,plain,(
    k1_xboole_0 = k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(global_subsumption,[],[f643,f1035])).

fof(f1035,plain,
    ( k1_xboole_0 = k4_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f1034,f169])).

fof(f1034,plain,
    ( k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) = k4_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f1033,f949])).

fof(f1033,plain,
    ( k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(sK0))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f1032,f128])).

fof(f128,plain,(
    k1_xboole_0 = k5_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(global_subsumption,[],[f32,f127])).

fof(f127,plain,
    ( k1_xboole_0 = k5_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f126,f36])).

fof(f126,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | k1_xboole_0 = k5_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f122,f37])).

fof(f122,plain,
    ( v1_xboole_0(k5_relat_1(k1_xboole_0,k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(duplicate_literal_removal,[],[f120])).

fof(f120,plain,
    ( v1_xboole_0(k5_relat_1(k1_xboole_0,k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f115,f43])).

fof(f115,plain,
    ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0))
    | v1_xboole_0(k5_relat_1(k1_xboole_0,k1_xboole_0)) ),
    inference(global_subsumption,[],[f32,f113])).

fof(f113,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0))
    | v1_xboole_0(k5_relat_1(k1_xboole_0,k1_xboole_0)) ),
    inference(superposition,[],[f42,f109])).

fof(f109,plain,(
    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)) ),
    inference(resolution,[],[f77,f32])).

fof(f77,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) ) ),
    inference(resolution,[],[f75,f36])).

fof(f1032,plain,
    ( k4_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k1_xboole_0))) = k5_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)),k4_relat_1(sK0))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f1023,f952])).

fof(f952,plain,(
    k1_xboole_0 = k5_relat_1(k4_relat_1(sK0),k1_xboole_0) ),
    inference(backward_demodulation,[],[f194,f949])).

fof(f194,plain,(
    k4_relat_1(k1_xboole_0) = k5_relat_1(k4_relat_1(sK0),k4_relat_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f193,f93])).

fof(f93,plain,(
    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    inference(global_subsumption,[],[f32,f92])).

fof(f92,plain,
    ( k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f91,f36])).

fof(f91,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    inference(resolution,[],[f88,f37])).

fof(f88,plain,
    ( v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(global_subsumption,[],[f30,f86])).

fof(f86,plain,
    ( v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f85,f43])).

fof(f85,plain,
    ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(global_subsumption,[],[f32,f84])).

fof(f84,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(superposition,[],[f42,f80])).

fof(f80,plain,(
    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(resolution,[],[f75,f30])).

fof(f193,plain,(
    k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k5_relat_1(k4_relat_1(sK0),k4_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f179,f32])).

fof(f179,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k4_relat_1(k5_relat_1(X0,sK0)) = k5_relat_1(k4_relat_1(sK0),k4_relat_1(X0)) ) ),
    inference(resolution,[],[f119,f36])).

fof(f119,plain,(
    ! [X7] :
      ( ~ v1_relat_1(X7)
      | k4_relat_1(k5_relat_1(X7,sK0)) = k5_relat_1(k4_relat_1(sK0),k4_relat_1(X7)) ) ),
    inference(resolution,[],[f41,f30])).

fof(f1023,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | k4_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k5_relat_1(k4_relat_1(sK0),k1_xboole_0)))) = k5_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1(k4_relat_1(sK0),k1_xboole_0))),k4_relat_1(sK0)) ),
    inference(backward_demodulation,[],[f672,f952])).

fof(f672,plain,
    ( ~ v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))
    | k4_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k5_relat_1(k4_relat_1(sK0),k1_xboole_0)))) = k5_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1(k4_relat_1(sK0),k1_xboole_0))),k4_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f526,f643])).

fof(f526,plain,
    ( ~ v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0)
    | k4_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k5_relat_1(k4_relat_1(sK0),k1_xboole_0)))) = k5_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1(k4_relat_1(sK0),k1_xboole_0))),k4_relat_1(sK0)) ),
    inference(resolution,[],[f512,f391])).

fof(f391,plain,(
    ! [X10] :
      ( ~ v1_xboole_0(X10)
      | k4_relat_1(k5_relat_1(sK0,X10)) = k5_relat_1(k4_relat_1(X10),k4_relat_1(sK0)) ) ),
    inference(resolution,[],[f116,f30])).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
      | ~ v1_xboole_0(X1) ) ),
    inference(resolution,[],[f41,f36])).

fof(f512,plain,
    ( v1_xboole_0(k5_relat_1(k1_xboole_0,k5_relat_1(k4_relat_1(sK0),k1_xboole_0)))
    | ~ v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f498,f43])).

fof(f498,plain,
    ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1(k4_relat_1(sK0),k1_xboole_0)))
    | v1_xboole_0(k5_relat_1(k1_xboole_0,k5_relat_1(k4_relat_1(sK0),k1_xboole_0))) ),
    inference(global_subsumption,[],[f32,f497])).

fof(f497,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1(k4_relat_1(sK0),k1_xboole_0)))
    | v1_xboole_0(k5_relat_1(k1_xboole_0,k5_relat_1(k4_relat_1(sK0),k1_xboole_0))) ),
    inference(superposition,[],[f42,f493])).

fof(f493,plain,(
    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1(k4_relat_1(sK0),k1_xboole_0))) ),
    inference(global_subsumption,[],[f32,f492])).

fof(f492,plain,
    ( k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1(k4_relat_1(sK0),k1_xboole_0)))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f490,f36])).

fof(f490,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1(k4_relat_1(sK0),k1_xboole_0))) ),
    inference(resolution,[],[f489,f38])).

fof(f489,plain,
    ( ~ v1_relat_1(k4_relat_1(k1_xboole_0))
    | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1(k4_relat_1(sK0),k1_xboole_0))) ),
    inference(global_subsumption,[],[f30,f487])).

fof(f487,plain,
    ( k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1(k4_relat_1(sK0),k1_xboole_0)))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f377,f43])).

fof(f377,plain,
    ( ~ v1_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK0))
    | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1(k4_relat_1(sK0),k1_xboole_0))) ),
    inference(resolution,[],[f371,f75])).

fof(f371,plain,
    ( v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))
    | ~ v1_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK0)) ),
    inference(superposition,[],[f38,f370])).

fof(f370,plain,(
    k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK0)) = k5_relat_1(k4_relat_1(sK0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f369,f55])).

fof(f369,plain,(
    k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK0)) = k5_relat_1(k4_relat_1(sK0),k4_relat_1(k4_relat_1(k1_xboole_0))) ),
    inference(resolution,[],[f359,f32])).

fof(f359,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k4_relat_1(k5_relat_1(k4_relat_1(X0),sK0)) = k5_relat_1(k4_relat_1(sK0),k4_relat_1(k4_relat_1(X0))) ) ),
    inference(resolution,[],[f180,f36])).

fof(f180,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | k4_relat_1(k5_relat_1(k4_relat_1(X1),sK0)) = k5_relat_1(k4_relat_1(sK0),k4_relat_1(k4_relat_1(X1))) ) ),
    inference(resolution,[],[f119,f38])).

fof(f294,plain,(
    k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
    inference(resolution,[],[f255,f32])).

fof(f255,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k5_relat_1(sK0,X0) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,X0))) ) ),
    inference(resolution,[],[f254,f36])).

fof(f95,plain,(
    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f31,f93])).

fof(f31,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:19:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (15345)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.47  % (15360)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.51  % (15338)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.51  % (15336)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.52  % (15340)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.53  % (15337)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (15339)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.53  % (15342)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.54  % (15344)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.54  % (15341)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.54  % (15348)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.55  % (15351)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.55  % (15359)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.56  % (15358)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.56  % (15350)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.56  % (15355)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.56  % (15361)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.56  % (15349)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.56  % (15347)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.57  % (15354)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.57  % (15346)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.57  % (15352)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.57  % (15343)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.58/0.57  % (15353)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.58/0.58  % (15356)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.58/0.58  % (15357)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.81/0.61  % (15348)Refutation found. Thanks to Tanya!
% 1.81/0.61  % SZS status Theorem for theBenchmark
% 1.81/0.61  % (15345)Refutation not found, incomplete strategy% (15345)------------------------------
% 1.81/0.61  % (15345)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.81/0.62  % SZS output start Proof for theBenchmark
% 1.81/0.62  fof(f1057,plain,(
% 1.81/0.62    $false),
% 1.81/0.62    inference(global_subsumption,[],[f95,f1056])).
% 1.81/0.62  fof(f1056,plain,(
% 1.81/0.62    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)),
% 1.81/0.62    inference(forward_demodulation,[],[f1037,f949])).
% 1.81/0.62  fof(f949,plain,(
% 1.81/0.62    k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 1.81/0.62    inference(forward_demodulation,[],[f939,f349])).
% 1.81/0.62  fof(f349,plain,(
% 1.81/0.62    k1_xboole_0 = k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0))),
% 1.81/0.62    inference(global_subsumption,[],[f32,f348])).
% 1.81/0.62  fof(f348,plain,(
% 1.81/0.62    k1_xboole_0 = k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0)),
% 1.81/0.62    inference(resolution,[],[f347,f36])).
% 1.81/0.62  fof(f36,plain,(
% 1.81/0.62    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 1.81/0.62    inference(cnf_transformation,[],[f16])).
% 1.81/0.62  fof(f16,plain,(
% 1.81/0.62    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 1.81/0.62    inference(ennf_transformation,[],[f5])).
% 1.81/0.62  fof(f5,axiom,(
% 1.81/0.62    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 1.81/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 1.81/0.62  fof(f347,plain,(
% 1.81/0.62    ~v1_relat_1(k1_xboole_0) | k1_xboole_0 = k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0))),
% 1.81/0.62    inference(duplicate_literal_removal,[],[f345])).
% 1.81/0.62  fof(f345,plain,(
% 1.81/0.62    ~v1_relat_1(k1_xboole_0) | k1_xboole_0 = k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)),
% 1.81/0.62    inference(resolution,[],[f218,f38])).
% 1.81/0.62  fof(f38,plain,(
% 1.81/0.62    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.81/0.62    inference(cnf_transformation,[],[f18])).
% 1.81/0.62  fof(f18,plain,(
% 1.81/0.62    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.81/0.62    inference(ennf_transformation,[],[f6])).
% 1.81/0.62  fof(f6,axiom,(
% 1.81/0.62    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 1.81/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 1.81/0.62  fof(f218,plain,(
% 1.81/0.62    ~v1_relat_1(k4_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | k1_xboole_0 = k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0))),
% 1.81/0.62    inference(resolution,[],[f216,f37])).
% 1.81/0.62  fof(f37,plain,(
% 1.81/0.62    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.81/0.62    inference(cnf_transformation,[],[f17])).
% 1.81/0.62  fof(f17,plain,(
% 1.81/0.62    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.81/0.62    inference(ennf_transformation,[],[f2])).
% 1.81/0.62  fof(f2,axiom,(
% 1.81/0.62    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.81/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.81/0.62  fof(f216,plain,(
% 1.81/0.62    v1_xboole_0(k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0))) | ~v1_relat_1(k4_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)),
% 1.81/0.62    inference(resolution,[],[f164,f43])).
% 1.81/0.62  fof(f43,plain,(
% 1.81/0.62    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.81/0.62    inference(cnf_transformation,[],[f25])).
% 1.81/0.62  fof(f25,plain,(
% 1.81/0.62    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.81/0.62    inference(flattening,[],[f24])).
% 1.81/0.62  fof(f24,plain,(
% 1.81/0.62    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 1.81/0.62    inference(ennf_transformation,[],[f7])).
% 1.81/0.62  fof(f7,axiom,(
% 1.81/0.62    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 1.81/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 1.81/0.62  fof(f164,plain,(
% 1.81/0.62    ~v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0))) | v1_xboole_0(k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0)))),
% 1.81/0.62    inference(global_subsumption,[],[f32,f163])).
% 1.81/0.62  fof(f163,plain,(
% 1.81/0.62    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0))) | v1_xboole_0(k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0)))),
% 1.81/0.62    inference(superposition,[],[f42,f158])).
% 1.81/0.62  fof(f158,plain,(
% 1.81/0.62    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0)))),
% 1.81/0.62    inference(resolution,[],[f143,f32])).
% 1.81/0.62  fof(f143,plain,(
% 1.81/0.62    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(X0)))) )),
% 1.81/0.62    inference(resolution,[],[f78,f36])).
% 1.81/0.62  fof(f78,plain,(
% 1.81/0.62    ( ! [X1] : (~v1_relat_1(X1) | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(X1)))) )),
% 1.81/0.62    inference(resolution,[],[f75,f38])).
% 1.81/0.62  fof(f75,plain,(
% 1.81/0.62    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0))) )),
% 1.81/0.62    inference(resolution,[],[f74,f62])).
% 1.81/0.62  fof(f62,plain,(
% 1.81/0.62    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.81/0.62    inference(resolution,[],[f46,f35])).
% 1.81/0.62  fof(f35,plain,(
% 1.81/0.62    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.81/0.62    inference(cnf_transformation,[],[f4])).
% 1.81/0.62  fof(f4,axiom,(
% 1.81/0.62    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.81/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.81/0.62  fof(f46,plain,(
% 1.81/0.62    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.81/0.62    inference(cnf_transformation,[],[f29])).
% 1.81/0.62  fof(f29,plain,(
% 1.81/0.62    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.81/0.62    inference(flattening,[],[f28])).
% 1.81/0.62  fof(f28,plain,(
% 1.81/0.62    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.81/0.62    inference(nnf_transformation,[],[f3])).
% 1.81/0.62  fof(f3,axiom,(
% 1.81/0.62    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.81/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.81/0.62  fof(f74,plain,(
% 1.81/0.62    ( ! [X0] : (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) | ~v1_relat_1(X0)) )),
% 1.81/0.62    inference(global_subsumption,[],[f32,f73])).
% 1.81/0.62  fof(f73,plain,(
% 1.81/0.62    ( ! [X0] : (~v1_relat_1(X0) | r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0) | ~v1_xboole_0(k1_xboole_0)) )),
% 1.81/0.62    inference(resolution,[],[f72,f36])).
% 1.81/0.62  fof(f72,plain,(
% 1.81/0.62    ( ! [X0] : (~v1_relat_1(k1_xboole_0) | ~v1_relat_1(X0) | r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X0)),k1_xboole_0)) )),
% 1.81/0.62    inference(superposition,[],[f40,f33])).
% 1.81/0.62  fof(f33,plain,(
% 1.81/0.62    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.81/0.62    inference(cnf_transformation,[],[f12])).
% 1.81/0.62  fof(f12,axiom,(
% 1.81/0.62    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.81/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 1.81/0.62  fof(f40,plain,(
% 1.81/0.62    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.81/0.62    inference(cnf_transformation,[],[f20])).
% 1.81/0.62  fof(f20,plain,(
% 1.81/0.62    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.81/0.62    inference(ennf_transformation,[],[f10])).
% 1.81/0.62  fof(f10,axiom,(
% 1.81/0.62    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 1.81/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).
% 1.81/0.62  fof(f42,plain,(
% 1.81/0.62    ( ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 1.81/0.62    inference(cnf_transformation,[],[f23])).
% 1.81/0.62  fof(f23,plain,(
% 1.81/0.62    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 1.81/0.62    inference(flattening,[],[f22])).
% 1.81/0.62  fof(f22,plain,(
% 1.81/0.62    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 1.81/0.62    inference(ennf_transformation,[],[f8])).
% 1.81/0.62  fof(f8,axiom,(
% 1.81/0.62    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k1_relat_1(X0)))),
% 1.81/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).
% 1.81/0.62  fof(f32,plain,(
% 1.81/0.62    v1_xboole_0(k1_xboole_0)),
% 1.81/0.62    inference(cnf_transformation,[],[f1])).
% 1.81/0.62  fof(f1,axiom,(
% 1.81/0.62    v1_xboole_0(k1_xboole_0)),
% 1.81/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.81/0.62  fof(f939,plain,(
% 1.81/0.62    k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0)) = k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(k1_xboole_0)))),
% 1.81/0.62    inference(resolution,[],[f698,f643])).
% 1.81/0.62  fof(f643,plain,(
% 1.81/0.62    v1_relat_1(k1_xboole_0)),
% 1.81/0.62    inference(subsumption_resolution,[],[f56,f642])).
% 1.81/0.62  fof(f642,plain,(
% 1.81/0.62    v1_relat_1(k4_relat_1(k1_xboole_0))),
% 1.81/0.62    inference(global_subsumption,[],[f32,f641])).
% 1.81/0.62  fof(f641,plain,(
% 1.81/0.62    v1_relat_1(k4_relat_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0)),
% 1.81/0.62    inference(forward_demodulation,[],[f640,f636])).
% 1.81/0.62  fof(f636,plain,(
% 1.81/0.62    k4_relat_1(k1_xboole_0) = k5_relat_1(sK0,k4_relat_1(k1_xboole_0))),
% 1.81/0.62    inference(forward_demodulation,[],[f633,f169])).
% 1.81/0.62  fof(f169,plain,(
% 1.81/0.62    k1_xboole_0 = k5_relat_1(k1_xboole_0,k4_relat_1(sK0))),
% 1.81/0.62    inference(global_subsumption,[],[f32,f168])).
% 1.81/0.62  fof(f168,plain,(
% 1.81/0.62    k1_xboole_0 = k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) | ~v1_xboole_0(k1_xboole_0)),
% 1.81/0.62    inference(resolution,[],[f167,f36])).
% 1.81/0.62  fof(f167,plain,(
% 1.81/0.62    ~v1_relat_1(k1_xboole_0) | k1_xboole_0 = k5_relat_1(k1_xboole_0,k4_relat_1(sK0))),
% 1.81/0.62    inference(global_subsumption,[],[f30,f165])).
% 1.81/0.62  fof(f165,plain,(
% 1.81/0.62    ~v1_relat_1(k1_xboole_0) | k1_xboole_0 = k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) | ~v1_relat_1(sK0)),
% 1.81/0.62    inference(resolution,[],[f157,f38])).
% 1.81/0.62  fof(f157,plain,(
% 1.81/0.62    ~v1_relat_1(k4_relat_1(sK0)) | ~v1_relat_1(k1_xboole_0) | k1_xboole_0 = k5_relat_1(k1_xboole_0,k4_relat_1(sK0))),
% 1.81/0.62    inference(resolution,[],[f152,f37])).
% 1.81/0.62  fof(f152,plain,(
% 1.81/0.62    v1_xboole_0(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) | ~v1_relat_1(k4_relat_1(sK0)) | ~v1_relat_1(k1_xboole_0)),
% 1.81/0.62    inference(resolution,[],[f151,f43])).
% 1.81/0.62  fof(f151,plain,(
% 1.81/0.62    ~v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) | v1_xboole_0(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))),
% 1.81/0.62    inference(global_subsumption,[],[f32,f150])).
% 1.81/0.62  fof(f150,plain,(
% 1.81/0.62    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) | v1_xboole_0(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))),
% 1.81/0.62    inference(superposition,[],[f42,f146])).
% 1.81/0.62  fof(f146,plain,(
% 1.81/0.62    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))),
% 1.81/0.62    inference(resolution,[],[f78,f30])).
% 1.81/0.62  fof(f30,plain,(
% 1.81/0.62    v1_relat_1(sK0)),
% 1.81/0.62    inference(cnf_transformation,[],[f27])).
% 1.81/0.62  fof(f27,plain,(
% 1.81/0.62    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 1.81/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f26])).
% 1.81/0.62  fof(f26,plain,(
% 1.81/0.62    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 1.81/0.62    introduced(choice_axiom,[])).
% 1.81/0.62  fof(f15,plain,(
% 1.81/0.62    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 1.81/0.62    inference(ennf_transformation,[],[f14])).
% 1.81/0.62  fof(f14,negated_conjecture,(
% 1.81/0.62    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 1.81/0.62    inference(negated_conjecture,[],[f13])).
% 1.81/0.62  fof(f13,conjecture,(
% 1.81/0.62    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 1.81/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).
% 1.81/0.62  fof(f633,plain,(
% 1.81/0.62    k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) = k5_relat_1(sK0,k4_relat_1(k1_xboole_0))),
% 1.81/0.62    inference(resolution,[],[f618,f32])).
% 1.81/0.62  fof(f618,plain,(
% 1.81/0.62    ( ! [X0] : (~v1_xboole_0(X0) | k5_relat_1(sK0,k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,k4_relat_1(sK0)))) )),
% 1.81/0.62    inference(resolution,[],[f617,f36])).
% 1.81/0.62  fof(f617,plain,(
% 1.81/0.62    ( ! [X12] : (~v1_relat_1(X12) | k4_relat_1(k5_relat_1(X12,k4_relat_1(sK0))) = k5_relat_1(sK0,k4_relat_1(X12))) )),
% 1.81/0.62    inference(forward_demodulation,[],[f612,f50])).
% 1.81/0.62  fof(f50,plain,(
% 1.81/0.62    sK0 = k4_relat_1(k4_relat_1(sK0))),
% 1.81/0.62    inference(resolution,[],[f39,f30])).
% 1.81/0.62  fof(f39,plain,(
% 1.81/0.62    ( ! [X0] : (~v1_relat_1(X0) | k4_relat_1(k4_relat_1(X0)) = X0) )),
% 1.81/0.62    inference(cnf_transformation,[],[f19])).
% 1.81/0.62  fof(f19,plain,(
% 1.81/0.62    ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 1.81/0.62    inference(ennf_transformation,[],[f9])).
% 1.81/0.62  fof(f9,axiom,(
% 1.81/0.62    ! [X0] : (v1_relat_1(X0) => k4_relat_1(k4_relat_1(X0)) = X0)),
% 1.81/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).
% 1.81/0.62  fof(f612,plain,(
% 1.81/0.62    ( ! [X12] : (~v1_relat_1(X12) | k4_relat_1(k5_relat_1(X12,k4_relat_1(sK0))) = k5_relat_1(k4_relat_1(k4_relat_1(sK0)),k4_relat_1(X12))) )),
% 1.81/0.62    inference(resolution,[],[f117,f30])).
% 1.81/0.62  fof(f117,plain,(
% 1.81/0.62    ( ! [X2,X3] : (~v1_relat_1(X3) | ~v1_relat_1(X2) | k4_relat_1(k5_relat_1(X2,k4_relat_1(X3))) = k5_relat_1(k4_relat_1(k4_relat_1(X3)),k4_relat_1(X2))) )),
% 1.81/0.62    inference(resolution,[],[f41,f38])).
% 1.81/0.62  fof(f41,plain,(
% 1.81/0.62    ( ! [X0,X1] : (~v1_relat_1(X1) | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.81/0.62    inference(cnf_transformation,[],[f21])).
% 1.81/0.62  fof(f21,plain,(
% 1.81/0.62    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.81/0.62    inference(ennf_transformation,[],[f11])).
% 1.81/0.62  fof(f11,axiom,(
% 1.81/0.62    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 1.81/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).
% 1.81/0.62  fof(f640,plain,(
% 1.81/0.62    ~v1_xboole_0(k1_xboole_0) | v1_relat_1(k5_relat_1(sK0,k4_relat_1(k1_xboole_0)))),
% 1.81/0.62    inference(forward_demodulation,[],[f637,f55])).
% 1.81/0.62  fof(f55,plain,(
% 1.81/0.62    k1_xboole_0 = k4_relat_1(k4_relat_1(k1_xboole_0))),
% 1.81/0.62    inference(resolution,[],[f51,f32])).
% 1.81/0.62  fof(f51,plain,(
% 1.81/0.62    ( ! [X0] : (~v1_xboole_0(X0) | k4_relat_1(k4_relat_1(X0)) = X0) )),
% 1.81/0.62    inference(resolution,[],[f39,f36])).
% 1.81/0.62  fof(f637,plain,(
% 1.81/0.62    ~v1_xboole_0(k4_relat_1(k4_relat_1(k1_xboole_0))) | v1_relat_1(k5_relat_1(sK0,k4_relat_1(k1_xboole_0)))),
% 1.81/0.62    inference(backward_demodulation,[],[f325,f636])).
% 1.81/0.62  fof(f325,plain,(
% 1.81/0.62    ~v1_xboole_0(k4_relat_1(k5_relat_1(sK0,k4_relat_1(k1_xboole_0)))) | v1_relat_1(k5_relat_1(sK0,k4_relat_1(k1_xboole_0)))),
% 1.81/0.62    inference(resolution,[],[f323,f36])).
% 1.81/0.62  fof(f323,plain,(
% 1.81/0.62    ~v1_relat_1(k4_relat_1(k5_relat_1(sK0,k4_relat_1(k1_xboole_0)))) | v1_relat_1(k5_relat_1(sK0,k4_relat_1(k1_xboole_0)))),
% 1.81/0.62    inference(superposition,[],[f38,f320])).
% 1.81/0.62  fof(f320,plain,(
% 1.81/0.62    k5_relat_1(sK0,k4_relat_1(k1_xboole_0)) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k4_relat_1(k1_xboole_0))))),
% 1.81/0.62    inference(resolution,[],[f310,f32])).
% 1.81/0.62  % (15345)Termination reason: Refutation not found, incomplete strategy
% 1.81/0.62  fof(f310,plain,(
% 1.81/0.62    ( ! [X0] : (~v1_xboole_0(X0) | k5_relat_1(sK0,k4_relat_1(X0)) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k4_relat_1(X0))))) )),
% 1.81/0.62    inference(resolution,[],[f256,f36])).
% 1.81/0.62  fof(f256,plain,(
% 1.81/0.62    ( ! [X1] : (~v1_relat_1(X1) | k5_relat_1(sK0,k4_relat_1(X1)) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k4_relat_1(X1))))) )),
% 1.81/0.62    inference(resolution,[],[f254,f38])).
% 1.81/0.62  fof(f254,plain,(
% 1.81/0.62    ( ! [X8] : (~v1_relat_1(X8) | k5_relat_1(sK0,X8) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,X8)))) )),
% 1.81/0.62    inference(resolution,[],[f59,f30])).
% 1.81/0.62  fof(f59,plain,(
% 1.81/0.62    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | k5_relat_1(X1,X0) = k4_relat_1(k4_relat_1(k5_relat_1(X1,X0)))) )),
% 1.81/0.62    inference(resolution,[],[f43,f39])).
% 1.81/0.62  fof(f56,plain,(
% 1.81/0.62    ~v1_relat_1(k4_relat_1(k1_xboole_0)) | v1_relat_1(k1_xboole_0)),
% 1.81/0.62    inference(superposition,[],[f38,f55])).
% 1.81/0.62  fof(f698,plain,(
% 1.81/0.62    ( ! [X4] : (~v1_relat_1(X4) | k4_relat_1(k5_relat_1(X4,k4_relat_1(k1_xboole_0))) = k5_relat_1(k1_xboole_0,k4_relat_1(X4))) )),
% 1.81/0.62    inference(forward_demodulation,[],[f684,f55])).
% 1.81/0.62  fof(f684,plain,(
% 1.81/0.62    ( ! [X4] : (~v1_relat_1(X4) | k4_relat_1(k5_relat_1(X4,k4_relat_1(k1_xboole_0))) = k5_relat_1(k4_relat_1(k4_relat_1(k1_xboole_0)),k4_relat_1(X4))) )),
% 1.81/0.62    inference(resolution,[],[f643,f117])).
% 1.81/0.62  fof(f1037,plain,(
% 1.81/0.62    k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k1_xboole_0)),
% 1.81/0.62    inference(backward_demodulation,[],[f294,f1036])).
% 1.81/0.62  
% 1.81/0.62  % (15345)Memory used [KB]: 6012
% 1.81/0.62  % (15345)Time elapsed: 0.200 s
% 1.81/0.62  % (15345)------------------------------
% 1.81/0.62  % (15345)------------------------------
% 1.81/0.62  fof(f1036,plain,(
% 1.81/0.62    k1_xboole_0 = k4_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 1.81/0.62    inference(global_subsumption,[],[f643,f1035])).
% 1.81/0.62  fof(f1035,plain,(
% 1.81/0.62    k1_xboole_0 = k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)),
% 1.81/0.62    inference(forward_demodulation,[],[f1034,f169])).
% 1.81/0.62  fof(f1034,plain,(
% 1.81/0.62    k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) = k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)),
% 1.81/0.62    inference(forward_demodulation,[],[f1033,f949])).
% 1.81/0.63  fof(f1033,plain,(
% 1.81/0.63    k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(sK0)) | ~v1_relat_1(k1_xboole_0)),
% 1.81/0.63    inference(forward_demodulation,[],[f1032,f128])).
% 1.81/0.63  fof(f128,plain,(
% 1.81/0.63    k1_xboole_0 = k5_relat_1(k1_xboole_0,k1_xboole_0)),
% 1.81/0.63    inference(global_subsumption,[],[f32,f127])).
% 1.81/0.63  fof(f127,plain,(
% 1.81/0.63    k1_xboole_0 = k5_relat_1(k1_xboole_0,k1_xboole_0) | ~v1_xboole_0(k1_xboole_0)),
% 1.81/0.63    inference(resolution,[],[f126,f36])).
% 1.81/0.63  fof(f126,plain,(
% 1.81/0.63    ~v1_relat_1(k1_xboole_0) | k1_xboole_0 = k5_relat_1(k1_xboole_0,k1_xboole_0)),
% 1.81/0.63    inference(resolution,[],[f122,f37])).
% 1.81/0.63  fof(f122,plain,(
% 1.81/0.63    v1_xboole_0(k5_relat_1(k1_xboole_0,k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)),
% 1.81/0.63    inference(duplicate_literal_removal,[],[f120])).
% 1.81/0.63  fof(f120,plain,(
% 1.81/0.63    v1_xboole_0(k5_relat_1(k1_xboole_0,k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 1.81/0.63    inference(resolution,[],[f115,f43])).
% 1.81/0.63  fof(f115,plain,(
% 1.81/0.63    ~v1_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)) | v1_xboole_0(k5_relat_1(k1_xboole_0,k1_xboole_0))),
% 1.81/0.63    inference(global_subsumption,[],[f32,f113])).
% 1.81/0.63  fof(f113,plain,(
% 1.81/0.63    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)) | v1_xboole_0(k5_relat_1(k1_xboole_0,k1_xboole_0))),
% 1.81/0.63    inference(superposition,[],[f42,f109])).
% 1.81/0.63  fof(f109,plain,(
% 1.81/0.63    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0))),
% 1.81/0.63    inference(resolution,[],[f77,f32])).
% 1.81/0.63  fof(f77,plain,(
% 1.81/0.63    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0))) )),
% 1.81/0.63    inference(resolution,[],[f75,f36])).
% 1.81/0.63  fof(f1032,plain,(
% 1.81/0.63    k4_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k1_xboole_0))) = k5_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0)),k4_relat_1(sK0)) | ~v1_relat_1(k1_xboole_0)),
% 1.81/0.63    inference(forward_demodulation,[],[f1023,f952])).
% 1.81/0.63  fof(f952,plain,(
% 1.81/0.63    k1_xboole_0 = k5_relat_1(k4_relat_1(sK0),k1_xboole_0)),
% 1.81/0.63    inference(backward_demodulation,[],[f194,f949])).
% 1.81/0.63  fof(f194,plain,(
% 1.81/0.63    k4_relat_1(k1_xboole_0) = k5_relat_1(k4_relat_1(sK0),k4_relat_1(k1_xboole_0))),
% 1.81/0.63    inference(forward_demodulation,[],[f193,f93])).
% 1.81/0.63  fof(f93,plain,(
% 1.81/0.63    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)),
% 1.81/0.63    inference(global_subsumption,[],[f32,f92])).
% 1.81/0.63  fof(f92,plain,(
% 1.81/0.63    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) | ~v1_xboole_0(k1_xboole_0)),
% 1.81/0.63    inference(resolution,[],[f91,f36])).
% 1.81/0.63  fof(f91,plain,(
% 1.81/0.63    ~v1_relat_1(k1_xboole_0) | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)),
% 1.81/0.63    inference(resolution,[],[f88,f37])).
% 1.81/0.63  fof(f88,plain,(
% 1.81/0.63    v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) | ~v1_relat_1(k1_xboole_0)),
% 1.81/0.63    inference(global_subsumption,[],[f30,f86])).
% 1.81/0.63  fof(f86,plain,(
% 1.81/0.63    v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) | ~v1_relat_1(sK0) | ~v1_relat_1(k1_xboole_0)),
% 1.81/0.63    inference(resolution,[],[f85,f43])).
% 1.81/0.63  fof(f85,plain,(
% 1.81/0.63    ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))),
% 1.81/0.63    inference(global_subsumption,[],[f32,f84])).
% 1.81/0.63  fof(f84,plain,(
% 1.81/0.63    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) | v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))),
% 1.81/0.63    inference(superposition,[],[f42,f80])).
% 1.81/0.63  fof(f80,plain,(
% 1.81/0.63    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 1.81/0.63    inference(resolution,[],[f75,f30])).
% 1.81/0.63  fof(f193,plain,(
% 1.81/0.63    k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k5_relat_1(k4_relat_1(sK0),k4_relat_1(k1_xboole_0))),
% 1.81/0.63    inference(resolution,[],[f179,f32])).
% 1.81/0.63  fof(f179,plain,(
% 1.81/0.63    ( ! [X0] : (~v1_xboole_0(X0) | k4_relat_1(k5_relat_1(X0,sK0)) = k5_relat_1(k4_relat_1(sK0),k4_relat_1(X0))) )),
% 1.81/0.63    inference(resolution,[],[f119,f36])).
% 1.81/0.63  fof(f119,plain,(
% 1.81/0.63    ( ! [X7] : (~v1_relat_1(X7) | k4_relat_1(k5_relat_1(X7,sK0)) = k5_relat_1(k4_relat_1(sK0),k4_relat_1(X7))) )),
% 1.81/0.63    inference(resolution,[],[f41,f30])).
% 1.81/0.63  fof(f1023,plain,(
% 1.81/0.63    ~v1_relat_1(k1_xboole_0) | k4_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k5_relat_1(k4_relat_1(sK0),k1_xboole_0)))) = k5_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1(k4_relat_1(sK0),k1_xboole_0))),k4_relat_1(sK0))),
% 1.81/0.63    inference(backward_demodulation,[],[f672,f952])).
% 1.81/0.63  fof(f672,plain,(
% 1.81/0.63    ~v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) | k4_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k5_relat_1(k4_relat_1(sK0),k1_xboole_0)))) = k5_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1(k4_relat_1(sK0),k1_xboole_0))),k4_relat_1(sK0))),
% 1.81/0.63    inference(subsumption_resolution,[],[f526,f643])).
% 1.81/0.63  fof(f526,plain,(
% 1.81/0.63    ~v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | k4_relat_1(k5_relat_1(sK0,k5_relat_1(k1_xboole_0,k5_relat_1(k4_relat_1(sK0),k1_xboole_0)))) = k5_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1(k4_relat_1(sK0),k1_xboole_0))),k4_relat_1(sK0))),
% 1.81/0.63    inference(resolution,[],[f512,f391])).
% 1.81/0.63  fof(f391,plain,(
% 1.81/0.63    ( ! [X10] : (~v1_xboole_0(X10) | k4_relat_1(k5_relat_1(sK0,X10)) = k5_relat_1(k4_relat_1(X10),k4_relat_1(sK0))) )),
% 1.81/0.63    inference(resolution,[],[f116,f30])).
% 1.81/0.63  fof(f116,plain,(
% 1.81/0.63    ( ! [X0,X1] : (~v1_relat_1(X0) | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_xboole_0(X1)) )),
% 1.81/0.63    inference(resolution,[],[f41,f36])).
% 1.81/0.63  fof(f512,plain,(
% 1.81/0.63    v1_xboole_0(k5_relat_1(k1_xboole_0,k5_relat_1(k4_relat_1(sK0),k1_xboole_0))) | ~v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)),
% 1.81/0.63    inference(resolution,[],[f498,f43])).
% 1.81/0.63  fof(f498,plain,(
% 1.81/0.63    ~v1_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1(k4_relat_1(sK0),k1_xboole_0))) | v1_xboole_0(k5_relat_1(k1_xboole_0,k5_relat_1(k4_relat_1(sK0),k1_xboole_0)))),
% 1.81/0.63    inference(global_subsumption,[],[f32,f497])).
% 1.81/0.63  fof(f497,plain,(
% 1.81/0.63    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1(k4_relat_1(sK0),k1_xboole_0))) | v1_xboole_0(k5_relat_1(k1_xboole_0,k5_relat_1(k4_relat_1(sK0),k1_xboole_0)))),
% 1.81/0.63    inference(superposition,[],[f42,f493])).
% 1.81/0.63  fof(f493,plain,(
% 1.81/0.63    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1(k4_relat_1(sK0),k1_xboole_0)))),
% 1.81/0.63    inference(global_subsumption,[],[f32,f492])).
% 1.81/0.63  fof(f492,plain,(
% 1.81/0.63    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1(k4_relat_1(sK0),k1_xboole_0))) | ~v1_xboole_0(k1_xboole_0)),
% 1.81/0.63    inference(resolution,[],[f490,f36])).
% 1.81/0.63  fof(f490,plain,(
% 1.81/0.63    ~v1_relat_1(k1_xboole_0) | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1(k4_relat_1(sK0),k1_xboole_0)))),
% 1.81/0.63    inference(resolution,[],[f489,f38])).
% 1.81/0.63  fof(f489,plain,(
% 1.81/0.63    ~v1_relat_1(k4_relat_1(k1_xboole_0)) | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1(k4_relat_1(sK0),k1_xboole_0)))),
% 1.81/0.63    inference(global_subsumption,[],[f30,f487])).
% 1.81/0.63  fof(f487,plain,(
% 1.81/0.63    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1(k4_relat_1(sK0),k1_xboole_0))) | ~v1_relat_1(sK0) | ~v1_relat_1(k4_relat_1(k1_xboole_0))),
% 1.81/0.63    inference(resolution,[],[f377,f43])).
% 1.81/0.63  fof(f377,plain,(
% 1.81/0.63    ~v1_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK0)) | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,k5_relat_1(k4_relat_1(sK0),k1_xboole_0)))),
% 1.81/0.63    inference(resolution,[],[f371,f75])).
% 1.81/0.63  fof(f371,plain,(
% 1.81/0.63    v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) | ~v1_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK0))),
% 1.81/0.63    inference(superposition,[],[f38,f370])).
% 1.81/0.63  fof(f370,plain,(
% 1.81/0.63    k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK0)) = k5_relat_1(k4_relat_1(sK0),k1_xboole_0)),
% 1.81/0.63    inference(forward_demodulation,[],[f369,f55])).
% 1.81/0.63  fof(f369,plain,(
% 1.81/0.63    k4_relat_1(k5_relat_1(k4_relat_1(k1_xboole_0),sK0)) = k5_relat_1(k4_relat_1(sK0),k4_relat_1(k4_relat_1(k1_xboole_0)))),
% 1.81/0.63    inference(resolution,[],[f359,f32])).
% 1.81/0.63  fof(f359,plain,(
% 1.81/0.63    ( ! [X0] : (~v1_xboole_0(X0) | k4_relat_1(k5_relat_1(k4_relat_1(X0),sK0)) = k5_relat_1(k4_relat_1(sK0),k4_relat_1(k4_relat_1(X0)))) )),
% 1.81/0.63    inference(resolution,[],[f180,f36])).
% 1.81/0.63  fof(f180,plain,(
% 1.81/0.63    ( ! [X1] : (~v1_relat_1(X1) | k4_relat_1(k5_relat_1(k4_relat_1(X1),sK0)) = k5_relat_1(k4_relat_1(sK0),k4_relat_1(k4_relat_1(X1)))) )),
% 1.81/0.63    inference(resolution,[],[f119,f38])).
% 1.81/0.63  fof(f294,plain,(
% 1.81/0.63    k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))),
% 1.81/0.63    inference(resolution,[],[f255,f32])).
% 1.81/0.63  fof(f255,plain,(
% 1.81/0.63    ( ! [X0] : (~v1_xboole_0(X0) | k5_relat_1(sK0,X0) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,X0)))) )),
% 1.81/0.63    inference(resolution,[],[f254,f36])).
% 1.81/0.63  fof(f95,plain,(
% 1.81/0.63    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)),
% 1.81/0.63    inference(subsumption_resolution,[],[f31,f93])).
% 1.81/0.63  fof(f31,plain,(
% 1.81/0.63    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 1.81/0.63    inference(cnf_transformation,[],[f27])).
% 1.81/0.63  % SZS output end Proof for theBenchmark
% 1.81/0.63  % (15348)------------------------------
% 1.81/0.63  % (15348)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.81/0.63  % (15348)Termination reason: Refutation
% 1.81/0.63  
% 1.81/0.63  % (15348)Memory used [KB]: 7164
% 1.81/0.63  % (15348)Time elapsed: 0.161 s
% 1.81/0.63  % (15348)------------------------------
% 1.81/0.63  % (15348)------------------------------
% 1.81/0.63  % (15335)Success in time 0.27 s
%------------------------------------------------------------------------------
