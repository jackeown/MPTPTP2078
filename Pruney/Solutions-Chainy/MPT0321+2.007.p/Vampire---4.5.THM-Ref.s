%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:29 EST 2020

% Result     : Theorem 2.16s
% Output     : Refutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :   91 (1105 expanded)
%              Number of leaves         :   12 ( 315 expanded)
%              Depth                    :   25
%              Number of atoms          :  167 (2857 expanded)
%              Number of equality atoms :  100 (2299 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3815,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3814,f3709])).

fof(f3709,plain,(
    ~ r1_tarski(sK3,sK1) ),
    inference(subsumption_resolution,[],[f2375,f3513])).

fof(f3513,plain,(
    sK1 != sK3 ),
    inference(subsumption_resolution,[],[f24,f3512])).

fof(f3512,plain,(
    sK0 = sK2 ),
    inference(global_subsumption,[],[f2719,f3509])).

fof(f3509,plain,(
    r1_tarski(sK0,sK2) ),
    inference(subsumption_resolution,[],[f3466,f39])).

fof(f39,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f3466,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))
    | r1_tarski(sK0,sK2) ),
    inference(superposition,[],[f2792,f3449])).

fof(f3449,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK1) ),
    inference(forward_demodulation,[],[f3408,f2744])).

fof(f2744,plain,(
    sK2 = k3_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f349,f2720])).

fof(f2720,plain,(
    sK0 = k2_xboole_0(sK2,sK0) ),
    inference(resolution,[],[f2718,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f2718,plain,(
    r1_tarski(sK2,sK0) ),
    inference(subsumption_resolution,[],[f2715,f23])).

fof(f23,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ( sK1 != sK3
      | sK0 != sK2 )
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( X1 != X3
          | X0 != X2 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) )
   => ( ( sK1 != sK3
        | sK0 != sK2 )
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
       => ( ( X1 = X3
            & X0 = X2 )
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(f2715,plain,
    ( r1_tarski(sK2,sK0)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f2608,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))
      | r1_tarski(X1,X2)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X1,X2)
      | ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
        & ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_tarski(X1,X2)
        & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
          | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(f2608,plain,(
    r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f561,f2561])).

fof(f2561,plain,(
    sK1 = k3_xboole_0(sK1,sK3) ),
    inference(superposition,[],[f29,f2376])).

fof(f2376,plain,(
    sK3 = k2_xboole_0(sK1,sK3) ),
    inference(resolution,[],[f2374,f30])).

fof(f2374,plain,(
    r1_tarski(sK1,sK3) ),
    inference(subsumption_resolution,[],[f2371,f22])).

fof(f22,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f18])).

fof(f2371,plain,
    ( r1_tarski(sK1,sK3)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f2323,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
      | r1_tarski(X1,X2)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2323,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)) ),
    inference(superposition,[],[f501,f2291])).

fof(f2291,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) ),
    inference(superposition,[],[f797,f683])).

fof(f683,plain,(
    ! [X5] : k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k2_xboole_0(X5,sK2),sK3)) ),
    inference(superposition,[],[f49,f130])).

fof(f130,plain,(
    ! [X0] : k2_zfmisc_1(k2_xboole_0(X0,sK2),sK3) = k2_xboole_0(k2_zfmisc_1(X0,sK3),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f34,f21])).

fof(f21,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f34,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[],[f29,f28])).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f797,plain,(
    ! [X14,X12,X13,X11] : k3_xboole_0(k2_zfmisc_1(X11,X13),k2_zfmisc_1(k2_xboole_0(X11,X12),X14)) = k2_zfmisc_1(X11,k3_xboole_0(X13,X14)) ),
    inference(superposition,[],[f38,f29])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f501,plain,(
    ! [X30,X31,X29] : r1_tarski(k2_zfmisc_1(X31,k3_xboole_0(X29,X30)),k2_zfmisc_1(X31,X30)) ),
    inference(superposition,[],[f470,f61])).

fof(f61,plain,(
    ! [X8,X7] : k2_xboole_0(k3_xboole_0(X7,X8),X8) = X8 ),
    inference(resolution,[],[f30,f41])).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f26,f27])).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f470,plain,(
    ! [X6,X4,X5] : r1_tarski(k2_zfmisc_1(X4,X5),k2_zfmisc_1(X4,k2_xboole_0(X5,X6))) ),
    inference(superposition,[],[f25,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f561,plain,(
    ! [X0] : r1_tarski(k2_zfmisc_1(sK2,k3_xboole_0(X0,sK3)),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f545,f27])).

fof(f545,plain,(
    ! [X0] : r1_tarski(k2_zfmisc_1(sK2,k3_xboole_0(sK3,X0)),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f500,f21])).

fof(f500,plain,(
    ! [X28,X26,X27] : r1_tarski(k2_zfmisc_1(X28,k3_xboole_0(X26,X27)),k2_zfmisc_1(X28,X26)) ),
    inference(superposition,[],[f470,f60])).

fof(f60,plain,(
    ! [X6,X5] : k2_xboole_0(k3_xboole_0(X5,X6),X5) = X5 ),
    inference(resolution,[],[f30,f26])).

fof(f349,plain,(
    ! [X6,X5] : k3_xboole_0(k2_xboole_0(X5,X6),X5) = X5 ),
    inference(superposition,[],[f247,f29])).

fof(f247,plain,(
    ! [X4,X3] : k3_xboole_0(X3,X4) = k3_xboole_0(X4,k3_xboole_0(X3,X4)) ),
    inference(superposition,[],[f89,f27])).

fof(f89,plain,(
    ! [X4,X3] : k3_xboole_0(X3,X4) = k3_xboole_0(k3_xboole_0(X3,X4),X4) ),
    inference(superposition,[],[f29,f61])).

fof(f3408,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1) ),
    inference(superposition,[],[f808,f764])).

fof(f764,plain,(
    ! [X5] : k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,k2_xboole_0(X5,sK3))) ),
    inference(superposition,[],[f49,f463])).

fof(f463,plain,(
    ! [X0] : k2_zfmisc_1(sK2,k2_xboole_0(X0,sK3)) = k2_xboole_0(k2_zfmisc_1(sK2,X0),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f35,f21])).

fof(f808,plain,(
    ! [X14,X12,X13,X11] : k3_xboole_0(k2_zfmisc_1(X13,X11),k2_zfmisc_1(X14,k2_xboole_0(X11,X12))) = k2_zfmisc_1(k3_xboole_0(X13,X14),X11) ),
    inference(superposition,[],[f38,f29])).

fof(f2792,plain,(
    ! [X4] :
      ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X4,sK1))
      | r1_tarski(sK0,X4) ) ),
    inference(backward_demodulation,[],[f2487,f2721])).

fof(f2721,plain,(
    sK0 = k2_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f2720,f28])).

fof(f2487,plain,(
    ! [X4] :
      ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X4,sK1))
      | r1_tarski(k2_xboole_0(sK0,sK2),X4) ) ),
    inference(forward_demodulation,[],[f2409,f21])).

fof(f2409,plain,(
    ! [X4] :
      ( ~ r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(X4,sK1))
      | r1_tarski(k2_xboole_0(sK0,sK2),X4) ) ),
    inference(backward_demodulation,[],[f750,f2376])).

fof(f750,plain,(
    ! [X4] :
      ( ~ r1_tarski(k2_zfmisc_1(sK2,k2_xboole_0(sK1,sK3)),k2_zfmisc_1(X4,sK1))
      | r1_tarski(k2_xboole_0(sK0,sK2),X4) ) ),
    inference(subsumption_resolution,[],[f738,f23])).

fof(f738,plain,(
    ! [X4] :
      ( ~ r1_tarski(k2_zfmisc_1(sK2,k2_xboole_0(sK1,sK3)),k2_zfmisc_1(X4,sK1))
      | r1_tarski(k2_xboole_0(sK0,sK2),X4)
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f36,f729])).

fof(f729,plain,(
    k2_zfmisc_1(k2_xboole_0(sK0,sK2),sK1) = k2_zfmisc_1(sK2,k2_xboole_0(sK1,sK3)) ),
    inference(forward_demodulation,[],[f707,f28])).

fof(f707,plain,(
    k2_zfmisc_1(k2_xboole_0(sK0,sK2),sK1) = k2_zfmisc_1(sK2,k2_xboole_0(sK3,sK1)) ),
    inference(superposition,[],[f462,f34])).

fof(f462,plain,(
    ! [X0] : k2_zfmisc_1(sK2,k2_xboole_0(sK3,X0)) = k2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X0)) ),
    inference(superposition,[],[f35,f21])).

fof(f2719,plain,
    ( ~ r1_tarski(sK0,sK2)
    | sK0 = sK2 ),
    inference(resolution,[],[f2718,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f24,plain,
    ( sK1 != sK3
    | sK0 != sK2 ),
    inference(cnf_transformation,[],[f18])).

fof(f2375,plain,
    ( ~ r1_tarski(sK3,sK1)
    | sK1 = sK3 ),
    inference(resolution,[],[f2374,f33])).

fof(f3814,plain,(
    r1_tarski(sK3,sK1) ),
    inference(subsumption_resolution,[],[f3707,f22])).

fof(f3707,plain,
    ( k1_xboole_0 = sK0
    | r1_tarski(sK3,sK1) ),
    inference(backward_demodulation,[],[f3503,f3512])).

fof(f3503,plain,
    ( r1_tarski(sK3,sK1)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f3458,f39])).

fof(f3458,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))
    | r1_tarski(sK3,sK1)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f619,f3449])).

fof(f619,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X0))
      | r1_tarski(sK3,X0)
      | k1_xboole_0 = sK2 ) ),
    inference(superposition,[],[f37,f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.06  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.06  % Command    : run_vampire %s %d
% 0.06/0.24  % Computer   : n021.cluster.edu
% 0.06/0.24  % Model      : x86_64 x86_64
% 0.06/0.24  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.06/0.24  % Memory     : 8042.1875MB
% 0.06/0.24  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.06/0.24  % CPULimit   : 60
% 0.06/0.24  % WCLimit    : 600
% 0.06/0.24  % DateTime   : Tue Dec  1 12:05:19 EST 2020
% 0.06/0.24  % CPUTime    : 
% 0.10/0.32  % (5498)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.10/0.33  % (5499)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.10/0.33  % (5503)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.10/0.33  % (5501)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.10/0.33  % (5513)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.10/0.33  % (5518)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.10/0.33  % (5497)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.10/0.34  % (5514)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.10/0.34  % (5496)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.10/0.34  % (5510)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.10/0.34  % (5520)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.10/0.34  % (5515)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.10/0.35  % (5500)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.10/0.35  % (5512)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.10/0.35  % (5506)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.10/0.35  % (5519)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.10/0.35  % (5502)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.10/0.35  % (5507)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.10/0.35  % (5495)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.10/0.36  % (5505)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.10/0.36  % (5508)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.10/0.36  % (5511)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.10/0.36  % (5509)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.10/0.36  % (5504)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.10/0.38  % (5516)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.10/0.39  % (5517)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 2.16/0.61  % (5498)Refutation found. Thanks to Tanya!
% 2.16/0.61  % SZS status Theorem for theBenchmark
% 2.76/0.62  % SZS output start Proof for theBenchmark
% 2.76/0.62  fof(f3815,plain,(
% 2.76/0.62    $false),
% 2.76/0.62    inference(subsumption_resolution,[],[f3814,f3709])).
% 2.76/0.62  fof(f3709,plain,(
% 2.76/0.62    ~r1_tarski(sK3,sK1)),
% 2.76/0.62    inference(subsumption_resolution,[],[f2375,f3513])).
% 2.76/0.62  fof(f3513,plain,(
% 2.76/0.62    sK1 != sK3),
% 2.76/0.62    inference(subsumption_resolution,[],[f24,f3512])).
% 2.76/0.62  fof(f3512,plain,(
% 2.76/0.62    sK0 = sK2),
% 2.76/0.62    inference(global_subsumption,[],[f2719,f3509])).
% 2.76/0.63  fof(f3509,plain,(
% 2.76/0.63    r1_tarski(sK0,sK2)),
% 2.76/0.63    inference(subsumption_resolution,[],[f3466,f39])).
% 2.76/0.63  fof(f39,plain,(
% 2.76/0.63    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.76/0.63    inference(equality_resolution,[],[f32])).
% 2.76/0.63  fof(f32,plain,(
% 2.76/0.63    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.76/0.63    inference(cnf_transformation,[],[f20])).
% 2.76/0.63  fof(f20,plain,(
% 2.76/0.63    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.76/0.63    inference(flattening,[],[f19])).
% 2.76/0.63  fof(f19,plain,(
% 2.76/0.63    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.76/0.63    inference(nnf_transformation,[],[f3])).
% 2.76/0.63  fof(f3,axiom,(
% 2.76/0.63    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.76/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.76/0.63  fof(f3466,plain,(
% 2.76/0.63    ~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) | r1_tarski(sK0,sK2)),
% 2.76/0.63    inference(superposition,[],[f2792,f3449])).
% 2.76/0.63  fof(f3449,plain,(
% 2.76/0.63    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK1)),
% 2.76/0.63    inference(forward_demodulation,[],[f3408,f2744])).
% 2.76/0.63  fof(f2744,plain,(
% 2.76/0.63    sK2 = k3_xboole_0(sK0,sK2)),
% 2.76/0.63    inference(superposition,[],[f349,f2720])).
% 2.76/0.63  fof(f2720,plain,(
% 2.76/0.63    sK0 = k2_xboole_0(sK2,sK0)),
% 2.76/0.63    inference(resolution,[],[f2718,f30])).
% 2.76/0.63  fof(f30,plain,(
% 2.76/0.63    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 2.76/0.63    inference(cnf_transformation,[],[f15])).
% 2.76/0.63  fof(f15,plain,(
% 2.76/0.63    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.76/0.63    inference(ennf_transformation,[],[f4])).
% 2.76/0.63  fof(f4,axiom,(
% 2.76/0.63    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.76/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.76/0.63  fof(f2718,plain,(
% 2.76/0.63    r1_tarski(sK2,sK0)),
% 2.76/0.63    inference(subsumption_resolution,[],[f2715,f23])).
% 2.76/0.63  fof(f23,plain,(
% 2.76/0.63    k1_xboole_0 != sK1),
% 2.76/0.63    inference(cnf_transformation,[],[f18])).
% 2.76/0.63  fof(f18,plain,(
% 2.76/0.63    (sK1 != sK3 | sK0 != sK2) & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3)),
% 2.76/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f17])).
% 2.76/0.63  fof(f17,plain,(
% 2.76/0.63    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)) => ((sK1 != sK3 | sK0 != sK2) & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3))),
% 2.76/0.63    introduced(choice_axiom,[])).
% 2.76/0.63  fof(f14,plain,(
% 2.76/0.63    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 2.76/0.63    inference(flattening,[],[f13])).
% 2.76/0.63  fof(f13,plain,(
% 2.76/0.63    ? [X0,X1,X2,X3] : (((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 2.76/0.63    inference(ennf_transformation,[],[f12])).
% 2.76/0.63  fof(f12,negated_conjecture,(
% 2.76/0.63    ~! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.76/0.63    inference(negated_conjecture,[],[f11])).
% 2.76/0.63  fof(f11,conjecture,(
% 2.76/0.63    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.76/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).
% 2.76/0.63  fof(f2715,plain,(
% 2.76/0.63    r1_tarski(sK2,sK0) | k1_xboole_0 = sK1),
% 2.76/0.63    inference(resolution,[],[f2608,f36])).
% 2.76/0.63  fof(f36,plain,(
% 2.76/0.63    ( ! [X2,X0,X1] : (~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) | r1_tarski(X1,X2) | k1_xboole_0 = X0) )),
% 2.76/0.63    inference(cnf_transformation,[],[f16])).
% 2.76/0.63  fof(f16,plain,(
% 2.76/0.63    ! [X0,X1,X2] : (r1_tarski(X1,X2) | (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) & ~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) | k1_xboole_0 = X0)),
% 2.76/0.63    inference(ennf_transformation,[],[f8])).
% 2.76/0.63  fof(f8,axiom,(
% 2.76/0.63    ! [X0,X1,X2] : ~(~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0)),
% 2.76/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_zfmisc_1)).
% 2.76/0.63  fof(f2608,plain,(
% 2.76/0.63    r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK0,sK1))),
% 2.76/0.63    inference(superposition,[],[f561,f2561])).
% 2.76/0.63  fof(f2561,plain,(
% 2.76/0.63    sK1 = k3_xboole_0(sK1,sK3)),
% 2.76/0.63    inference(superposition,[],[f29,f2376])).
% 2.76/0.63  fof(f2376,plain,(
% 2.76/0.63    sK3 = k2_xboole_0(sK1,sK3)),
% 2.76/0.63    inference(resolution,[],[f2374,f30])).
% 2.76/0.63  fof(f2374,plain,(
% 2.76/0.63    r1_tarski(sK1,sK3)),
% 2.76/0.63    inference(subsumption_resolution,[],[f2371,f22])).
% 2.76/0.63  fof(f22,plain,(
% 2.76/0.63    k1_xboole_0 != sK0),
% 2.76/0.63    inference(cnf_transformation,[],[f18])).
% 2.76/0.63  fof(f2371,plain,(
% 2.76/0.63    r1_tarski(sK1,sK3) | k1_xboole_0 = sK0),
% 2.76/0.63    inference(resolution,[],[f2323,f37])).
% 2.76/0.63  fof(f37,plain,(
% 2.76/0.63    ( ! [X2,X0,X1] : (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(X1,X2) | k1_xboole_0 = X0) )),
% 2.76/0.63    inference(cnf_transformation,[],[f16])).
% 2.76/0.63  fof(f2323,plain,(
% 2.76/0.63    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3))),
% 2.76/0.63    inference(superposition,[],[f501,f2291])).
% 2.76/0.63  fof(f2291,plain,(
% 2.76/0.63    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))),
% 2.76/0.63    inference(superposition,[],[f797,f683])).
% 2.76/0.63  fof(f683,plain,(
% 2.76/0.63    ( ! [X5] : (k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k2_xboole_0(X5,sK2),sK3))) )),
% 2.76/0.63    inference(superposition,[],[f49,f130])).
% 2.76/0.63  fof(f130,plain,(
% 2.76/0.63    ( ! [X0] : (k2_zfmisc_1(k2_xboole_0(X0,sK2),sK3) = k2_xboole_0(k2_zfmisc_1(X0,sK3),k2_zfmisc_1(sK0,sK1))) )),
% 2.76/0.63    inference(superposition,[],[f34,f21])).
% 2.76/0.63  fof(f21,plain,(
% 2.76/0.63    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3)),
% 2.76/0.63    inference(cnf_transformation,[],[f18])).
% 2.76/0.63  fof(f34,plain,(
% 2.76/0.63    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 2.76/0.63    inference(cnf_transformation,[],[f9])).
% 2.76/0.63  fof(f9,axiom,(
% 2.76/0.63    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 2.76/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).
% 2.76/0.63  fof(f49,plain,(
% 2.76/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X0)) = X0) )),
% 2.76/0.63    inference(superposition,[],[f29,f28])).
% 2.76/0.63  fof(f28,plain,(
% 2.76/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.76/0.63    inference(cnf_transformation,[],[f1])).
% 2.76/0.63  fof(f1,axiom,(
% 2.76/0.63    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.76/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.76/0.63  fof(f797,plain,(
% 2.76/0.63    ( ! [X14,X12,X13,X11] : (k3_xboole_0(k2_zfmisc_1(X11,X13),k2_zfmisc_1(k2_xboole_0(X11,X12),X14)) = k2_zfmisc_1(X11,k3_xboole_0(X13,X14))) )),
% 2.76/0.63    inference(superposition,[],[f38,f29])).
% 2.76/0.63  fof(f38,plain,(
% 2.76/0.63    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 2.76/0.63    inference(cnf_transformation,[],[f10])).
% 2.76/0.63  fof(f10,axiom,(
% 2.76/0.63    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 2.76/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 2.76/0.63  fof(f501,plain,(
% 2.76/0.63    ( ! [X30,X31,X29] : (r1_tarski(k2_zfmisc_1(X31,k3_xboole_0(X29,X30)),k2_zfmisc_1(X31,X30))) )),
% 2.76/0.63    inference(superposition,[],[f470,f61])).
% 2.76/0.63  fof(f61,plain,(
% 2.76/0.63    ( ! [X8,X7] : (k2_xboole_0(k3_xboole_0(X7,X8),X8) = X8) )),
% 2.76/0.63    inference(resolution,[],[f30,f41])).
% 2.76/0.63  fof(f41,plain,(
% 2.76/0.63    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) )),
% 2.76/0.63    inference(superposition,[],[f26,f27])).
% 2.76/0.63  fof(f27,plain,(
% 2.76/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.76/0.63    inference(cnf_transformation,[],[f2])).
% 2.76/0.63  fof(f2,axiom,(
% 2.76/0.63    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.76/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.76/0.63  fof(f26,plain,(
% 2.76/0.63    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.76/0.63    inference(cnf_transformation,[],[f5])).
% 2.76/0.63  fof(f5,axiom,(
% 2.76/0.63    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 2.76/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 2.76/0.63  fof(f470,plain,(
% 2.76/0.63    ( ! [X6,X4,X5] : (r1_tarski(k2_zfmisc_1(X4,X5),k2_zfmisc_1(X4,k2_xboole_0(X5,X6)))) )),
% 2.76/0.63    inference(superposition,[],[f25,f35])).
% 2.76/0.63  fof(f35,plain,(
% 2.76/0.63    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 2.76/0.63    inference(cnf_transformation,[],[f9])).
% 2.76/0.63  fof(f25,plain,(
% 2.76/0.63    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.76/0.63    inference(cnf_transformation,[],[f7])).
% 2.76/0.63  fof(f7,axiom,(
% 2.76/0.63    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.76/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.76/0.63  fof(f29,plain,(
% 2.76/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 2.76/0.63    inference(cnf_transformation,[],[f6])).
% 2.76/0.63  fof(f6,axiom,(
% 2.76/0.63    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 2.76/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).
% 2.76/0.63  fof(f561,plain,(
% 2.76/0.63    ( ! [X0] : (r1_tarski(k2_zfmisc_1(sK2,k3_xboole_0(X0,sK3)),k2_zfmisc_1(sK0,sK1))) )),
% 2.76/0.63    inference(superposition,[],[f545,f27])).
% 2.76/0.63  fof(f545,plain,(
% 2.76/0.63    ( ! [X0] : (r1_tarski(k2_zfmisc_1(sK2,k3_xboole_0(sK3,X0)),k2_zfmisc_1(sK0,sK1))) )),
% 2.76/0.63    inference(superposition,[],[f500,f21])).
% 2.76/0.63  fof(f500,plain,(
% 2.76/0.63    ( ! [X28,X26,X27] : (r1_tarski(k2_zfmisc_1(X28,k3_xboole_0(X26,X27)),k2_zfmisc_1(X28,X26))) )),
% 2.76/0.63    inference(superposition,[],[f470,f60])).
% 2.76/0.63  fof(f60,plain,(
% 2.76/0.63    ( ! [X6,X5] : (k2_xboole_0(k3_xboole_0(X5,X6),X5) = X5) )),
% 2.76/0.63    inference(resolution,[],[f30,f26])).
% 2.76/0.63  fof(f349,plain,(
% 2.76/0.63    ( ! [X6,X5] : (k3_xboole_0(k2_xboole_0(X5,X6),X5) = X5) )),
% 2.76/0.63    inference(superposition,[],[f247,f29])).
% 2.76/0.63  fof(f247,plain,(
% 2.76/0.63    ( ! [X4,X3] : (k3_xboole_0(X3,X4) = k3_xboole_0(X4,k3_xboole_0(X3,X4))) )),
% 2.76/0.63    inference(superposition,[],[f89,f27])).
% 2.76/0.63  fof(f89,plain,(
% 2.76/0.63    ( ! [X4,X3] : (k3_xboole_0(X3,X4) = k3_xboole_0(k3_xboole_0(X3,X4),X4)) )),
% 2.76/0.63    inference(superposition,[],[f29,f61])).
% 2.76/0.63  fof(f3408,plain,(
% 2.76/0.63    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1)),
% 2.76/0.63    inference(superposition,[],[f808,f764])).
% 2.76/0.63  fof(f764,plain,(
% 2.76/0.63    ( ! [X5] : (k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,k2_xboole_0(X5,sK3)))) )),
% 2.76/0.63    inference(superposition,[],[f49,f463])).
% 2.76/0.63  fof(f463,plain,(
% 2.76/0.63    ( ! [X0] : (k2_zfmisc_1(sK2,k2_xboole_0(X0,sK3)) = k2_xboole_0(k2_zfmisc_1(sK2,X0),k2_zfmisc_1(sK0,sK1))) )),
% 2.76/0.63    inference(superposition,[],[f35,f21])).
% 2.76/0.63  fof(f808,plain,(
% 2.76/0.63    ( ! [X14,X12,X13,X11] : (k3_xboole_0(k2_zfmisc_1(X13,X11),k2_zfmisc_1(X14,k2_xboole_0(X11,X12))) = k2_zfmisc_1(k3_xboole_0(X13,X14),X11)) )),
% 2.76/0.63    inference(superposition,[],[f38,f29])).
% 2.76/0.63  fof(f2792,plain,(
% 2.76/0.63    ( ! [X4] : (~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X4,sK1)) | r1_tarski(sK0,X4)) )),
% 2.76/0.63    inference(backward_demodulation,[],[f2487,f2721])).
% 2.76/0.63  fof(f2721,plain,(
% 2.76/0.63    sK0 = k2_xboole_0(sK0,sK2)),
% 2.76/0.63    inference(superposition,[],[f2720,f28])).
% 2.76/0.63  fof(f2487,plain,(
% 2.76/0.63    ( ! [X4] : (~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X4,sK1)) | r1_tarski(k2_xboole_0(sK0,sK2),X4)) )),
% 2.76/0.63    inference(forward_demodulation,[],[f2409,f21])).
% 2.76/0.63  fof(f2409,plain,(
% 2.76/0.63    ( ! [X4] : (~r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(X4,sK1)) | r1_tarski(k2_xboole_0(sK0,sK2),X4)) )),
% 2.76/0.63    inference(backward_demodulation,[],[f750,f2376])).
% 2.76/0.63  fof(f750,plain,(
% 2.76/0.63    ( ! [X4] : (~r1_tarski(k2_zfmisc_1(sK2,k2_xboole_0(sK1,sK3)),k2_zfmisc_1(X4,sK1)) | r1_tarski(k2_xboole_0(sK0,sK2),X4)) )),
% 2.76/0.63    inference(subsumption_resolution,[],[f738,f23])).
% 2.76/0.63  fof(f738,plain,(
% 2.76/0.63    ( ! [X4] : (~r1_tarski(k2_zfmisc_1(sK2,k2_xboole_0(sK1,sK3)),k2_zfmisc_1(X4,sK1)) | r1_tarski(k2_xboole_0(sK0,sK2),X4) | k1_xboole_0 = sK1) )),
% 2.76/0.63    inference(superposition,[],[f36,f729])).
% 2.76/0.63  fof(f729,plain,(
% 2.76/0.63    k2_zfmisc_1(k2_xboole_0(sK0,sK2),sK1) = k2_zfmisc_1(sK2,k2_xboole_0(sK1,sK3))),
% 2.76/0.63    inference(forward_demodulation,[],[f707,f28])).
% 2.76/0.63  fof(f707,plain,(
% 2.76/0.63    k2_zfmisc_1(k2_xboole_0(sK0,sK2),sK1) = k2_zfmisc_1(sK2,k2_xboole_0(sK3,sK1))),
% 2.76/0.63    inference(superposition,[],[f462,f34])).
% 2.76/0.63  fof(f462,plain,(
% 2.76/0.63    ( ! [X0] : (k2_zfmisc_1(sK2,k2_xboole_0(sK3,X0)) = k2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X0))) )),
% 2.76/0.63    inference(superposition,[],[f35,f21])).
% 2.76/0.63  fof(f2719,plain,(
% 2.76/0.63    ~r1_tarski(sK0,sK2) | sK0 = sK2),
% 2.76/0.63    inference(resolution,[],[f2718,f33])).
% 2.76/0.63  fof(f33,plain,(
% 2.76/0.63    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 2.76/0.63    inference(cnf_transformation,[],[f20])).
% 2.76/0.63  fof(f24,plain,(
% 2.76/0.63    sK1 != sK3 | sK0 != sK2),
% 2.76/0.63    inference(cnf_transformation,[],[f18])).
% 2.76/0.63  fof(f2375,plain,(
% 2.76/0.63    ~r1_tarski(sK3,sK1) | sK1 = sK3),
% 2.76/0.63    inference(resolution,[],[f2374,f33])).
% 2.76/0.63  fof(f3814,plain,(
% 2.76/0.63    r1_tarski(sK3,sK1)),
% 2.76/0.63    inference(subsumption_resolution,[],[f3707,f22])).
% 2.76/0.63  fof(f3707,plain,(
% 2.76/0.63    k1_xboole_0 = sK0 | r1_tarski(sK3,sK1)),
% 2.76/0.63    inference(backward_demodulation,[],[f3503,f3512])).
% 2.76/0.63  fof(f3503,plain,(
% 2.76/0.63    r1_tarski(sK3,sK1) | k1_xboole_0 = sK2),
% 2.76/0.63    inference(subsumption_resolution,[],[f3458,f39])).
% 2.76/0.63  fof(f3458,plain,(
% 2.76/0.63    ~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) | r1_tarski(sK3,sK1) | k1_xboole_0 = sK2),
% 2.76/0.63    inference(superposition,[],[f619,f3449])).
% 2.76/0.63  fof(f619,plain,(
% 2.76/0.63    ( ! [X0] : (~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X0)) | r1_tarski(sK3,X0) | k1_xboole_0 = sK2) )),
% 2.76/0.63    inference(superposition,[],[f37,f21])).
% 2.76/0.63  % SZS output end Proof for theBenchmark
% 2.76/0.63  % (5498)------------------------------
% 2.76/0.63  % (5498)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.76/0.63  % (5498)Termination reason: Refutation
% 2.76/0.63  
% 2.76/0.63  % (5498)Memory used [KB]: 9850
% 2.76/0.63  % (5498)Time elapsed: 0.304 s
% 2.76/0.63  % (5498)------------------------------
% 2.76/0.63  % (5498)------------------------------
% 2.76/0.63  % (5494)Success in time 0.381 s
%------------------------------------------------------------------------------
