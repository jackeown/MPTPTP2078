%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:52 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 261 expanded)
%              Number of leaves         :   14 (  90 expanded)
%              Depth                    :   15
%              Number of atoms          :  123 ( 402 expanded)
%              Number of equality atoms :   31 ( 175 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f867,plain,(
    $false ),
    inference(subsumption_resolution,[],[f866,f41])).

fof(f41,plain,(
    ~ r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK1)))) ),
    inference(definition_unfolding,[],[f26,f40,f40])).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f33,f34])).

fof(f34,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f26,plain,(
    ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f21,f20])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(X1)))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relat_1)).

fof(f866,plain,(
    r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK1)))) ),
    inference(forward_demodulation,[],[f855,f45])).

fof(f45,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f31,f34,f34])).

fof(f31,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f855,plain,(
    r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK0)))) ),
    inference(resolution,[],[f437,f543])).

fof(f543,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,sK1))),k1_relat_1(sK1)) ),
    inference(superposition,[],[f533,f45])).

fof(f533,plain,(
    ! [X3] : r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X3))),k1_relat_1(sK1)) ),
    inference(superposition,[],[f58,f487])).

fof(f487,plain,(
    ! [X1] : k1_relat_1(sK1) = k3_tarski(k2_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X1))))) ),
    inference(forward_demodulation,[],[f486,f96])).

fof(f96,plain,(
    ! [X4,X5] : k3_tarski(k2_enumset1(X4,X4,X4,k1_setfam_1(k2_enumset1(X4,X4,X4,X5)))) = X4 ),
    inference(forward_demodulation,[],[f94,f45])).

fof(f94,plain,(
    ! [X4,X5] : k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(X4,X4,X4,X5)),k1_setfam_1(k2_enumset1(X4,X4,X4,X5)),k1_setfam_1(k2_enumset1(X4,X4,X4,X5)),X4)) = X4 ),
    inference(resolution,[],[f46,f44])).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f30,f40])).

fof(f30,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1 ) ),
    inference(definition_unfolding,[],[f35,f39])).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f32,f34])).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f35,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f486,plain,(
    ! [X1] : k3_tarski(k2_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X1))))) = k1_relat_1(k3_tarski(k2_enumset1(sK1,sK1,sK1,k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X1))))) ),
    inference(forward_demodulation,[],[f485,f45])).

fof(f485,plain,(
    ! [X1] : k1_relat_1(k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X1)),k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X1)),k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X1)),sK1))) = k3_tarski(k2_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X1))))) ),
    inference(forward_demodulation,[],[f469,f45])).

fof(f469,plain,(
    ! [X1] : k1_relat_1(k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X1)),k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X1)),k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X1)),sK1))) = k3_tarski(k2_enumset1(k1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X1))),k1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X1))),k1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X1))),k1_relat_1(sK1))) ),
    inference(resolution,[],[f336,f55])).

fof(f55,plain,(
    ! [X1] : v1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X1))) ),
    inference(resolution,[],[f52,f25])).

fof(f25,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ) ),
    inference(resolution,[],[f49,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f49,plain,(
    ! [X0,X1] : m1_subset_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f44,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f336,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k3_tarski(k2_enumset1(X1,X1,X1,sK1))) = k3_tarski(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(sK1))) ) ),
    inference(resolution,[],[f42,f25])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k3_tarski(k2_enumset1(X0,X0,X0,X1))) = k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f27,f39,f39])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relat_1)).

fof(f58,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_enumset1(X1,X1,X1,X0))) ),
    inference(superposition,[],[f43,f45])).

fof(f43,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f29,f39])).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f437,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X1))),X2)
      | r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X1))),k1_setfam_1(k2_enumset1(X2,X2,X2,k1_relat_1(sK0)))) ) ),
    inference(resolution,[],[f430,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X2)
      | r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f38,f40])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f430,plain,(
    ! [X3] : r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X3))),k1_relat_1(sK0)) ),
    inference(superposition,[],[f58,f372])).

fof(f372,plain,(
    ! [X0] : k1_relat_1(sK0) = k3_tarski(k2_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0))))) ),
    inference(forward_demodulation,[],[f371,f96])).

fof(f371,plain,(
    ! [X0] : k3_tarski(k2_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0))))) = k1_relat_1(k3_tarski(k2_enumset1(sK0,sK0,sK0,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0))))) ),
    inference(forward_demodulation,[],[f370,f45])).

fof(f370,plain,(
    ! [X0] : k1_relat_1(k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0)),k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0)),k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0)),sK0))) = k3_tarski(k2_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0))))) ),
    inference(forward_demodulation,[],[f353,f45])).

fof(f353,plain,(
    ! [X0] : k1_relat_1(k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0)),k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0)),k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0)),sK0))) = k3_tarski(k2_enumset1(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0))),k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0))),k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0))),k1_relat_1(sK0))) ),
    inference(resolution,[],[f335,f54])).

fof(f54,plain,(
    ! [X0] : v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0))) ),
    inference(resolution,[],[f52,f24])).

fof(f24,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f335,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(k3_tarski(k2_enumset1(X0,X0,X0,sK0))) = k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(sK0))) ) ),
    inference(resolution,[],[f42,f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:49:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.42  % (13395)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.44  % (13393)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.45  % (13395)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f867,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(subsumption_resolution,[],[f866,f41])).
% 0.21/0.45  fof(f41,plain,(
% 0.21/0.45    ~r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK1))))),
% 0.21/0.45    inference(definition_unfolding,[],[f26,f40,f40])).
% 0.21/0.45  fof(f40,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 0.21/0.45    inference(definition_unfolding,[],[f33,f34])).
% 0.21/0.45  fof(f34,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f6])).
% 0.21/0.45  fof(f6,axiom,(
% 0.21/0.45    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).
% 0.21/0.45  fof(f33,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f8])).
% 0.21/0.45  fof(f8,axiom,(
% 0.21/0.45    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.45  fof(f26,plain,(
% 0.21/0.45    ~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))),
% 0.21/0.45    inference(cnf_transformation,[],[f22])).
% 0.21/0.45  fof(f22,plain,(
% 0.21/0.45    (~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f21,f20])).
% 0.21/0.45  fof(f20,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    ? [X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(X1))) & v1_relat_1(X1)) => (~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) & v1_relat_1(sK1))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f14,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f13])).
% 0.21/0.45  fof(f13,negated_conjecture,(
% 0.21/0.45    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))))),
% 0.21/0.45    inference(negated_conjecture,[],[f12])).
% 0.21/0.45  fof(f12,conjecture,(
% 0.21/0.45    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relat_1)).
% 0.21/0.45  fof(f866,plain,(
% 0.21/0.45    r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK1))))),
% 0.21/0.45    inference(forward_demodulation,[],[f855,f45])).
% 0.21/0.45  fof(f45,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 0.21/0.45    inference(definition_unfolding,[],[f31,f34,f34])).
% 0.21/0.45  fof(f31,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f5])).
% 0.21/0.45  fof(f5,axiom,(
% 0.21/0.45    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.45  fof(f855,plain,(
% 0.21/0.45    r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK0))))),
% 0.21/0.45    inference(resolution,[],[f437,f543])).
% 0.21/0.45  fof(f543,plain,(
% 0.21/0.45    ( ! [X0] : (r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,sK1))),k1_relat_1(sK1))) )),
% 0.21/0.45    inference(superposition,[],[f533,f45])).
% 0.21/0.45  fof(f533,plain,(
% 0.21/0.45    ( ! [X3] : (r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X3))),k1_relat_1(sK1))) )),
% 0.21/0.45    inference(superposition,[],[f58,f487])).
% 0.21/0.45  fof(f487,plain,(
% 0.21/0.45    ( ! [X1] : (k1_relat_1(sK1) = k3_tarski(k2_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X1)))))) )),
% 0.21/0.45    inference(forward_demodulation,[],[f486,f96])).
% 0.21/0.45  fof(f96,plain,(
% 0.21/0.45    ( ! [X4,X5] : (k3_tarski(k2_enumset1(X4,X4,X4,k1_setfam_1(k2_enumset1(X4,X4,X4,X5)))) = X4) )),
% 0.21/0.45    inference(forward_demodulation,[],[f94,f45])).
% 0.21/0.45  fof(f94,plain,(
% 0.21/0.45    ( ! [X4,X5] : (k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(X4,X4,X4,X5)),k1_setfam_1(k2_enumset1(X4,X4,X4,X5)),k1_setfam_1(k2_enumset1(X4,X4,X4,X5)),X4)) = X4) )),
% 0.21/0.45    inference(resolution,[],[f46,f44])).
% 0.21/0.45  fof(f44,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0)) )),
% 0.21/0.45    inference(definition_unfolding,[],[f30,f40])).
% 0.21/0.45  fof(f30,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.21/0.45  fof(f46,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1) )),
% 0.21/0.45    inference(definition_unfolding,[],[f35,f39])).
% 0.21/0.45  fof(f39,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 0.21/0.45    inference(definition_unfolding,[],[f32,f34])).
% 0.21/0.45  fof(f32,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f7])).
% 0.21/0.45  fof(f7,axiom,(
% 0.21/0.45    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.45  fof(f35,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f17])).
% 0.21/0.45  fof(f17,plain,(
% 0.21/0.45    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.45  fof(f486,plain,(
% 0.21/0.45    ( ! [X1] : (k3_tarski(k2_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X1))))) = k1_relat_1(k3_tarski(k2_enumset1(sK1,sK1,sK1,k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X1)))))) )),
% 0.21/0.45    inference(forward_demodulation,[],[f485,f45])).
% 0.21/0.45  fof(f485,plain,(
% 0.21/0.45    ( ! [X1] : (k1_relat_1(k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X1)),k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X1)),k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X1)),sK1))) = k3_tarski(k2_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X1)))))) )),
% 0.21/0.45    inference(forward_demodulation,[],[f469,f45])).
% 0.21/0.45  fof(f469,plain,(
% 0.21/0.45    ( ! [X1] : (k1_relat_1(k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X1)),k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X1)),k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X1)),sK1))) = k3_tarski(k2_enumset1(k1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X1))),k1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X1))),k1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X1))),k1_relat_1(sK1)))) )),
% 0.21/0.45    inference(resolution,[],[f336,f55])).
% 0.21/0.45  fof(f55,plain,(
% 0.21/0.45    ( ! [X1] : (v1_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,X1)))) )),
% 0.21/0.45    inference(resolution,[],[f52,f25])).
% 0.21/0.45  fof(f25,plain,(
% 0.21/0.45    v1_relat_1(sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f22])).
% 0.21/0.45  fof(f52,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) )),
% 0.21/0.45    inference(resolution,[],[f49,f28])).
% 0.21/0.45  fof(f28,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f16])).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f10])).
% 0.21/0.45  fof(f10,axiom,(
% 0.21/0.45    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.45  fof(f49,plain,(
% 0.21/0.45    ( ! [X0,X1] : (m1_subset_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_zfmisc_1(X0))) )),
% 0.21/0.45    inference(resolution,[],[f44,f37])).
% 0.21/0.45  fof(f37,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f23])).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.45    inference(nnf_transformation,[],[f9])).
% 0.21/0.45  fof(f9,axiom,(
% 0.21/0.45    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.45  fof(f336,plain,(
% 0.21/0.45    ( ! [X1] : (~v1_relat_1(X1) | k1_relat_1(k3_tarski(k2_enumset1(X1,X1,X1,sK1))) = k3_tarski(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(sK1)))) )),
% 0.21/0.45    inference(resolution,[],[f42,f25])).
% 0.21/0.45  fof(f42,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k3_tarski(k2_enumset1(X0,X0,X0,X1))) = k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X0)) )),
% 0.21/0.45    inference(definition_unfolding,[],[f27,f39,f39])).
% 0.21/0.45  fof(f27,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f15])).
% 0.21/0.45  fof(f15,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f11])).
% 0.21/0.45  fof(f11,axiom,(
% 0.21/0.45    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relat_1)).
% 0.21/0.45  fof(f58,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_enumset1(X1,X1,X1,X0)))) )),
% 0.21/0.45    inference(superposition,[],[f43,f45])).
% 0.21/0.45  fof(f43,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) )),
% 0.21/0.45    inference(definition_unfolding,[],[f29,f39])).
% 0.21/0.45  fof(f29,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f4])).
% 0.21/0.45  fof(f4,axiom,(
% 0.21/0.45    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.45  fof(f437,plain,(
% 0.21/0.45    ( ! [X2,X1] : (~r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X1))),X2) | r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X1))),k1_setfam_1(k2_enumset1(X2,X2,X2,k1_relat_1(sK0))))) )),
% 0.21/0.45    inference(resolution,[],[f430,f47])).
% 0.21/0.45  fof(f47,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~r1_tarski(X0,X2) | r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) | ~r1_tarski(X0,X1)) )),
% 0.21/0.45    inference(definition_unfolding,[],[f38,f40])).
% 0.21/0.45  fof(f38,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f19])).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.45    inference(flattening,[],[f18])).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.45    inference(ennf_transformation,[],[f3])).
% 0.21/0.45  fof(f3,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.21/0.45  fof(f430,plain,(
% 0.21/0.45    ( ! [X3] : (r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X3))),k1_relat_1(sK0))) )),
% 0.21/0.45    inference(superposition,[],[f58,f372])).
% 0.21/0.45  fof(f372,plain,(
% 0.21/0.45    ( ! [X0] : (k1_relat_1(sK0) = k3_tarski(k2_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0)))))) )),
% 0.21/0.45    inference(forward_demodulation,[],[f371,f96])).
% 0.21/0.45  fof(f371,plain,(
% 0.21/0.45    ( ! [X0] : (k3_tarski(k2_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0))))) = k1_relat_1(k3_tarski(k2_enumset1(sK0,sK0,sK0,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0)))))) )),
% 0.21/0.45    inference(forward_demodulation,[],[f370,f45])).
% 0.21/0.45  fof(f370,plain,(
% 0.21/0.45    ( ! [X0] : (k1_relat_1(k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0)),k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0)),k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0)),sK0))) = k3_tarski(k2_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0)))))) )),
% 0.21/0.45    inference(forward_demodulation,[],[f353,f45])).
% 0.21/0.45  fof(f353,plain,(
% 0.21/0.45    ( ! [X0] : (k1_relat_1(k3_tarski(k2_enumset1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0)),k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0)),k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0)),sK0))) = k3_tarski(k2_enumset1(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0))),k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0))),k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0))),k1_relat_1(sK0)))) )),
% 0.21/0.45    inference(resolution,[],[f335,f54])).
% 0.21/0.45  fof(f54,plain,(
% 0.21/0.45    ( ! [X0] : (v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,X0)))) )),
% 0.21/0.45    inference(resolution,[],[f52,f24])).
% 0.21/0.45  fof(f24,plain,(
% 0.21/0.45    v1_relat_1(sK0)),
% 0.21/0.45    inference(cnf_transformation,[],[f22])).
% 0.21/0.45  fof(f335,plain,(
% 0.21/0.45    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(k3_tarski(k2_enumset1(X0,X0,X0,sK0))) = k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(sK0)))) )),
% 0.21/0.45    inference(resolution,[],[f42,f24])).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (13395)------------------------------
% 0.21/0.45  % (13395)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (13395)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (13395)Memory used [KB]: 2302
% 0.21/0.45  % (13395)Time elapsed: 0.033 s
% 0.21/0.45  % (13395)------------------------------
% 0.21/0.45  % (13395)------------------------------
% 0.21/0.45  % (13382)Success in time 0.09 s
%------------------------------------------------------------------------------
