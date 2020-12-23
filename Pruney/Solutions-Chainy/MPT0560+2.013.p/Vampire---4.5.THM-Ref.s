%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:01 EST 2020

% Result     : Theorem 2.78s
% Output     : Refutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 271 expanded)
%              Number of leaves         :   14 (  87 expanded)
%              Depth                    :   15
%              Number of atoms          :  174 ( 739 expanded)
%              Number of equality atoms :   45 ( 216 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3822,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3821,f304])).

fof(f304,plain,(
    ! [X6,X5] : r1_tarski(k9_relat_1(k7_relat_1(sK0,X5),X6),k9_relat_1(sK0,X6)) ),
    inference(subsumption_resolution,[],[f300,f124])).

fof(f124,plain,(
    ! [X0] : r1_tarski(k7_relat_1(sK0,X0),sK0) ),
    inference(subsumption_resolution,[],[f122,f37])).

fof(f37,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1)
    & r1_tarski(sK1,sK2)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f33,f32])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k9_relat_1(k7_relat_1(X0,X2),X1) != k9_relat_1(X0,X1)
            & r1_tarski(X1,X2) )
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( k9_relat_1(k7_relat_1(sK0,X2),X1) != k9_relat_1(sK0,X1)
          & r1_tarski(X1,X2) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X2,X1] :
        ( k9_relat_1(k7_relat_1(sK0,X2),X1) != k9_relat_1(sK0,X1)
        & r1_tarski(X1,X2) )
   => ( k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1)
      & r1_tarski(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k9_relat_1(k7_relat_1(X0,X2),X1) != k9_relat_1(X0,X1)
          & r1_tarski(X1,X2) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1,X2] :
            ( r1_tarski(X1,X2)
           => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

fof(f122,plain,(
    ! [X0] :
      ( r1_tarski(k7_relat_1(sK0,X0),sK0)
      | ~ v1_relat_1(sK0) ) ),
    inference(superposition,[],[f67,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f67,plain,(
    ! [X5] : r1_tarski(k5_relat_1(k6_relat_1(X5),sK0),sK0) ),
    inference(resolution,[],[f37,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).

fof(f300,plain,(
    ! [X6,X5] :
      ( ~ r1_tarski(k7_relat_1(sK0,X5),sK0)
      | r1_tarski(k9_relat_1(k7_relat_1(sK0,X5),X6),k9_relat_1(sK0,X6)) ) ),
    inference(resolution,[],[f72,f62])).

fof(f62,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK0,X0)) ),
    inference(resolution,[],[f37,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f72,plain,(
    ! [X14,X13] :
      ( ~ v1_relat_1(X13)
      | ~ r1_tarski(X13,sK0)
      | r1_tarski(k9_relat_1(X13,X14),k9_relat_1(sK0,X14)) ) ),
    inference(resolution,[],[f37,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_relat_1)).

fof(f3821,plain,(
    ~ r1_tarski(k9_relat_1(k7_relat_1(sK0,sK2),sK1),k9_relat_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f3815,f39])).

fof(f39,plain,(
    k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f3815,plain,
    ( k9_relat_1(k7_relat_1(sK0,sK2),sK1) = k9_relat_1(sK0,sK1)
    | ~ r1_tarski(k9_relat_1(k7_relat_1(sK0,sK2),sK1),k9_relat_1(sK0,sK1)) ),
    inference(resolution,[],[f3790,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f3790,plain,(
    r1_tarski(k9_relat_1(sK0,sK1),k9_relat_1(k7_relat_1(sK0,sK2),sK1)) ),
    inference(superposition,[],[f3726,f319])).

fof(f319,plain,(
    ! [X5] : k9_relat_1(k7_relat_1(sK0,X5),X5) = k9_relat_1(sK0,X5) ),
    inference(forward_demodulation,[],[f318,f65])).

fof(f65,plain,(
    ! [X3] : k2_relat_1(k7_relat_1(sK0,X3)) = k9_relat_1(sK0,X3) ),
    inference(resolution,[],[f37,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f318,plain,(
    ! [X5] : k9_relat_1(k7_relat_1(sK0,X5),X5) = k2_relat_1(k7_relat_1(sK0,X5)) ),
    inference(subsumption_resolution,[],[f315,f62])).

fof(f315,plain,(
    ! [X5] :
      ( k9_relat_1(k7_relat_1(sK0,X5),X5) = k2_relat_1(k7_relat_1(sK0,X5))
      | ~ v1_relat_1(k7_relat_1(sK0,X5)) ) ),
    inference(superposition,[],[f48,f106])).

fof(f106,plain,(
    ! [X0] : k7_relat_1(sK0,X0) = k7_relat_1(k7_relat_1(sK0,X0),X0) ),
    inference(subsumption_resolution,[],[f97,f62])).

fof(f97,plain,(
    ! [X0] :
      ( k7_relat_1(sK0,X0) = k7_relat_1(k7_relat_1(sK0,X0),X0)
      | ~ v1_relat_1(k7_relat_1(sK0,X0)) ) ),
    inference(resolution,[],[f63,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

fof(f63,plain,(
    ! [X1] : r1_tarski(k1_relat_1(k7_relat_1(sK0,X1)),X1) ),
    inference(resolution,[],[f37,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(f3726,plain,(
    ! [X7] : r1_tarski(k9_relat_1(k7_relat_1(sK0,sK1),X7),k9_relat_1(k7_relat_1(sK0,sK2),X7)) ),
    inference(superposition,[],[f3615,f171])).

fof(f171,plain,(
    k7_relat_1(sK0,sK1) = k7_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(subsumption_resolution,[],[f164,f62])).

fof(f164,plain,
    ( k7_relat_1(sK0,sK1) = k7_relat_1(k7_relat_1(sK0,sK1),sK2)
    | ~ v1_relat_1(k7_relat_1(sK0,sK1)) ),
    inference(resolution,[],[f141,f51])).

fof(f141,plain,(
    r1_tarski(k1_relat_1(k7_relat_1(sK0,sK1)),sK2) ),
    inference(resolution,[],[f74,f63])).

fof(f74,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,sK1)
      | r1_tarski(X1,sK2) ) ),
    inference(resolution,[],[f38,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f38,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f3615,plain,(
    ! [X4,X2,X3] : r1_tarski(k9_relat_1(k7_relat_1(k7_relat_1(sK0,X4),X2),X3),k9_relat_1(k7_relat_1(sK0,X2),X3)) ),
    inference(backward_demodulation,[],[f1015,f594])).

fof(f594,plain,(
    ! [X6,X4,X5] : k9_relat_1(k7_relat_1(sK0,X5),k9_relat_1(k6_relat_1(X4),X6)) = k9_relat_1(k7_relat_1(k7_relat_1(sK0,X5),X4),X6) ),
    inference(subsumption_resolution,[],[f593,f40])).

fof(f40,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f593,plain,(
    ! [X6,X4,X5] :
      ( k9_relat_1(k7_relat_1(sK0,X5),k9_relat_1(k6_relat_1(X4),X6)) = k9_relat_1(k7_relat_1(k7_relat_1(sK0,X5),X4),X6)
      | ~ v1_relat_1(k6_relat_1(X4)) ) ),
    inference(subsumption_resolution,[],[f592,f62])).

fof(f592,plain,(
    ! [X6,X4,X5] :
      ( k9_relat_1(k7_relat_1(sK0,X5),k9_relat_1(k6_relat_1(X4),X6)) = k9_relat_1(k7_relat_1(k7_relat_1(sK0,X5),X4),X6)
      | ~ v1_relat_1(k7_relat_1(sK0,X5))
      | ~ v1_relat_1(k6_relat_1(X4)) ) ),
    inference(superposition,[],[f52,f82])).

fof(f82,plain,(
    ! [X6,X7] : k7_relat_1(k7_relat_1(sK0,X6),X7) = k5_relat_1(k6_relat_1(X7),k7_relat_1(sK0,X6)) ),
    inference(resolution,[],[f62,f47])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t159_relat_1)).

fof(f1015,plain,(
    ! [X4,X2,X3] : r1_tarski(k9_relat_1(k7_relat_1(sK0,X4),k9_relat_1(k6_relat_1(X2),X3)),k9_relat_1(k7_relat_1(sK0,X2),X3)) ),
    inference(superposition,[],[f304,f183])).

fof(f183,plain,(
    ! [X2,X3] : k9_relat_1(sK0,k9_relat_1(k6_relat_1(X2),X3)) = k9_relat_1(k7_relat_1(sK0,X2),X3) ),
    inference(subsumption_resolution,[],[f182,f40])).

fof(f182,plain,(
    ! [X2,X3] :
      ( k9_relat_1(sK0,k9_relat_1(k6_relat_1(X2),X3)) = k9_relat_1(k7_relat_1(sK0,X2),X3)
      | ~ v1_relat_1(k6_relat_1(X2)) ) ),
    inference(subsumption_resolution,[],[f181,f37])).

fof(f181,plain,(
    ! [X2,X3] :
      ( k9_relat_1(sK0,k9_relat_1(k6_relat_1(X2),X3)) = k9_relat_1(k7_relat_1(sK0,X2),X3)
      | ~ v1_relat_1(sK0)
      | ~ v1_relat_1(k6_relat_1(X2)) ) ),
    inference(superposition,[],[f52,f64])).

fof(f64,plain,(
    ! [X2] : k7_relat_1(sK0,X2) = k5_relat_1(k6_relat_1(X2),sK0) ),
    inference(resolution,[],[f37,f47])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:49:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (24531)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.48  % (24528)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.48  % (24536)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.49  % (24530)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.50  % (24541)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.50  % (24548)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.50  % (24539)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.50  % (24527)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.50  % (24532)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.50  % (24546)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.50  % (24540)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (24545)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.50  % (24552)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.51  % (24547)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.51  % (24538)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.51  % (24533)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.51  % (24549)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.51  % (24535)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.51  % (24542)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.52  % (24551)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.52  % (24534)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.52  % (24544)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.53  % (24529)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.54  % (24550)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.54  % (24543)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.55  % (24537)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 2.78/0.77  % (24535)Refutation found. Thanks to Tanya!
% 2.78/0.77  % SZS status Theorem for theBenchmark
% 2.78/0.77  % SZS output start Proof for theBenchmark
% 2.78/0.77  fof(f3822,plain,(
% 2.78/0.77    $false),
% 2.78/0.77    inference(subsumption_resolution,[],[f3821,f304])).
% 2.78/0.77  fof(f304,plain,(
% 2.78/0.77    ( ! [X6,X5] : (r1_tarski(k9_relat_1(k7_relat_1(sK0,X5),X6),k9_relat_1(sK0,X6))) )),
% 2.78/0.77    inference(subsumption_resolution,[],[f300,f124])).
% 2.78/0.77  fof(f124,plain,(
% 2.78/0.77    ( ! [X0] : (r1_tarski(k7_relat_1(sK0,X0),sK0)) )),
% 2.78/0.77    inference(subsumption_resolution,[],[f122,f37])).
% 2.78/0.77  fof(f37,plain,(
% 2.78/0.77    v1_relat_1(sK0)),
% 2.78/0.77    inference(cnf_transformation,[],[f34])).
% 2.78/0.77  fof(f34,plain,(
% 2.78/0.77    (k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1) & r1_tarski(sK1,sK2)) & v1_relat_1(sK0)),
% 2.78/0.77    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f33,f32])).
% 2.78/0.77  fof(f32,plain,(
% 2.78/0.77    ? [X0] : (? [X1,X2] : (k9_relat_1(k7_relat_1(X0,X2),X1) != k9_relat_1(X0,X1) & r1_tarski(X1,X2)) & v1_relat_1(X0)) => (? [X2,X1] : (k9_relat_1(k7_relat_1(sK0,X2),X1) != k9_relat_1(sK0,X1) & r1_tarski(X1,X2)) & v1_relat_1(sK0))),
% 2.78/0.77    introduced(choice_axiom,[])).
% 3.29/0.77  fof(f33,plain,(
% 3.29/0.77    ? [X2,X1] : (k9_relat_1(k7_relat_1(sK0,X2),X1) != k9_relat_1(sK0,X1) & r1_tarski(X1,X2)) => (k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1) & r1_tarski(sK1,sK2))),
% 3.29/0.77    introduced(choice_axiom,[])).
% 3.29/0.77  fof(f17,plain,(
% 3.29/0.77    ? [X0] : (? [X1,X2] : (k9_relat_1(k7_relat_1(X0,X2),X1) != k9_relat_1(X0,X1) & r1_tarski(X1,X2)) & v1_relat_1(X0))),
% 3.29/0.77    inference(ennf_transformation,[],[f16])).
% 3.29/0.77  fof(f16,negated_conjecture,(
% 3.29/0.77    ~! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)))),
% 3.29/0.77    inference(negated_conjecture,[],[f15])).
% 3.29/0.77  fof(f15,conjecture,(
% 3.29/0.77    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)))),
% 3.29/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).
% 3.29/0.77  fof(f122,plain,(
% 3.29/0.77    ( ! [X0] : (r1_tarski(k7_relat_1(sK0,X0),sK0) | ~v1_relat_1(sK0)) )),
% 3.29/0.77    inference(superposition,[],[f67,f47])).
% 3.29/0.77  fof(f47,plain,(
% 3.29/0.77    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 3.29/0.77    inference(cnf_transformation,[],[f22])).
% 3.29/0.77  fof(f22,plain,(
% 3.29/0.77    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 3.29/0.77    inference(ennf_transformation,[],[f12])).
% 3.29/0.77  fof(f12,axiom,(
% 3.29/0.77    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 3.29/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 3.29/0.77  fof(f67,plain,(
% 3.29/0.77    ( ! [X5] : (r1_tarski(k5_relat_1(k6_relat_1(X5),sK0),sK0)) )),
% 3.29/0.77    inference(resolution,[],[f37,f50])).
% 3.29/0.77  fof(f50,plain,(
% 3.29/0.77    ( ! [X0,X1] : (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) | ~v1_relat_1(X1)) )),
% 3.29/0.77    inference(cnf_transformation,[],[f24])).
% 3.29/0.77  fof(f24,plain,(
% 3.29/0.77    ! [X0,X1] : ((r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) | ~v1_relat_1(X1))),
% 3.29/0.77    inference(ennf_transformation,[],[f10])).
% 3.29/0.77  fof(f10,axiom,(
% 3.29/0.77    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 3.29/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).
% 3.29/0.77  fof(f300,plain,(
% 3.29/0.77    ( ! [X6,X5] : (~r1_tarski(k7_relat_1(sK0,X5),sK0) | r1_tarski(k9_relat_1(k7_relat_1(sK0,X5),X6),k9_relat_1(sK0,X6))) )),
% 3.29/0.77    inference(resolution,[],[f72,f62])).
% 3.29/0.77  fof(f62,plain,(
% 3.29/0.77    ( ! [X0] : (v1_relat_1(k7_relat_1(sK0,X0))) )),
% 3.29/0.77    inference(resolution,[],[f37,f45])).
% 3.29/0.77  fof(f45,plain,(
% 3.29/0.77    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 3.29/0.77    inference(cnf_transformation,[],[f20])).
% 3.29/0.77  fof(f20,plain,(
% 3.29/0.77    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 3.29/0.77    inference(ennf_transformation,[],[f4])).
% 3.29/0.77  fof(f4,axiom,(
% 3.29/0.77    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 3.29/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 3.29/0.77  fof(f72,plain,(
% 3.29/0.77    ( ! [X14,X13] : (~v1_relat_1(X13) | ~r1_tarski(X13,sK0) | r1_tarski(k9_relat_1(X13,X14),k9_relat_1(sK0,X14))) )),
% 3.29/0.77    inference(resolution,[],[f37,f53])).
% 3.29/0.77  fof(f53,plain,(
% 3.29/0.77    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 3.29/0.77    inference(cnf_transformation,[],[f29])).
% 3.29/0.77  fof(f29,plain,(
% 3.29/0.77    ! [X0,X1] : (! [X2] : (r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 3.29/0.77    inference(flattening,[],[f28])).
% 3.29/0.77  fof(f28,plain,(
% 3.29/0.77    ! [X0,X1] : (! [X2] : ((r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 3.29/0.77    inference(ennf_transformation,[],[f7])).
% 3.29/0.77  fof(f7,axiom,(
% 3.29/0.77    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)))))),
% 3.29/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_relat_1)).
% 3.29/0.77  fof(f3821,plain,(
% 3.29/0.77    ~r1_tarski(k9_relat_1(k7_relat_1(sK0,sK2),sK1),k9_relat_1(sK0,sK1))),
% 3.29/0.77    inference(subsumption_resolution,[],[f3815,f39])).
% 3.29/0.77  fof(f39,plain,(
% 3.29/0.77    k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1)),
% 3.29/0.77    inference(cnf_transformation,[],[f34])).
% 3.29/0.77  fof(f3815,plain,(
% 3.29/0.77    k9_relat_1(k7_relat_1(sK0,sK2),sK1) = k9_relat_1(sK0,sK1) | ~r1_tarski(k9_relat_1(k7_relat_1(sK0,sK2),sK1),k9_relat_1(sK0,sK1))),
% 3.29/0.77    inference(resolution,[],[f3790,f56])).
% 3.29/0.77  fof(f56,plain,(
% 3.29/0.77    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.29/0.77    inference(cnf_transformation,[],[f36])).
% 3.29/0.77  fof(f36,plain,(
% 3.29/0.77    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.29/0.77    inference(flattening,[],[f35])).
% 3.29/0.77  fof(f35,plain,(
% 3.29/0.77    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.29/0.77    inference(nnf_transformation,[],[f1])).
% 3.29/0.77  fof(f1,axiom,(
% 3.29/0.77    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.29/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.29/0.77  fof(f3790,plain,(
% 3.29/0.77    r1_tarski(k9_relat_1(sK0,sK1),k9_relat_1(k7_relat_1(sK0,sK2),sK1))),
% 3.29/0.77    inference(superposition,[],[f3726,f319])).
% 3.29/0.77  fof(f319,plain,(
% 3.29/0.77    ( ! [X5] : (k9_relat_1(k7_relat_1(sK0,X5),X5) = k9_relat_1(sK0,X5)) )),
% 3.29/0.77    inference(forward_demodulation,[],[f318,f65])).
% 3.29/0.77  fof(f65,plain,(
% 3.29/0.77    ( ! [X3] : (k2_relat_1(k7_relat_1(sK0,X3)) = k9_relat_1(sK0,X3)) )),
% 3.29/0.77    inference(resolution,[],[f37,f48])).
% 3.29/0.77  fof(f48,plain,(
% 3.29/0.77    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.29/0.77    inference(cnf_transformation,[],[f23])).
% 3.29/0.77  fof(f23,plain,(
% 3.29/0.77    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.29/0.77    inference(ennf_transformation,[],[f6])).
% 3.29/0.77  fof(f6,axiom,(
% 3.29/0.77    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 3.29/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 3.29/0.77  fof(f318,plain,(
% 3.29/0.77    ( ! [X5] : (k9_relat_1(k7_relat_1(sK0,X5),X5) = k2_relat_1(k7_relat_1(sK0,X5))) )),
% 3.29/0.77    inference(subsumption_resolution,[],[f315,f62])).
% 3.29/0.77  fof(f315,plain,(
% 3.29/0.77    ( ! [X5] : (k9_relat_1(k7_relat_1(sK0,X5),X5) = k2_relat_1(k7_relat_1(sK0,X5)) | ~v1_relat_1(k7_relat_1(sK0,X5))) )),
% 3.29/0.77    inference(superposition,[],[f48,f106])).
% 3.29/0.77  fof(f106,plain,(
% 3.29/0.77    ( ! [X0] : (k7_relat_1(sK0,X0) = k7_relat_1(k7_relat_1(sK0,X0),X0)) )),
% 3.29/0.77    inference(subsumption_resolution,[],[f97,f62])).
% 3.29/0.77  fof(f97,plain,(
% 3.29/0.77    ( ! [X0] : (k7_relat_1(sK0,X0) = k7_relat_1(k7_relat_1(sK0,X0),X0) | ~v1_relat_1(k7_relat_1(sK0,X0))) )),
% 3.29/0.77    inference(resolution,[],[f63,f51])).
% 3.29/0.77  fof(f51,plain,(
% 3.29/0.77    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.29/0.77    inference(cnf_transformation,[],[f26])).
% 3.29/0.77  fof(f26,plain,(
% 3.29/0.77    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.29/0.77    inference(flattening,[],[f25])).
% 3.29/0.77  fof(f25,plain,(
% 3.29/0.77    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.29/0.77    inference(ennf_transformation,[],[f13])).
% 3.29/0.77  fof(f13,axiom,(
% 3.29/0.77    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 3.29/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).
% 3.29/0.77  fof(f63,plain,(
% 3.29/0.77    ( ! [X1] : (r1_tarski(k1_relat_1(k7_relat_1(sK0,X1)),X1)) )),
% 3.29/0.77    inference(resolution,[],[f37,f46])).
% 3.29/0.77  fof(f46,plain,(
% 3.29/0.77    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 3.29/0.77    inference(cnf_transformation,[],[f21])).
% 3.29/0.77  fof(f21,plain,(
% 3.29/0.77    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 3.29/0.77    inference(ennf_transformation,[],[f11])).
% 3.29/0.77  fof(f11,axiom,(
% 3.29/0.77    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 3.29/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).
% 3.29/0.77  fof(f3726,plain,(
% 3.29/0.77    ( ! [X7] : (r1_tarski(k9_relat_1(k7_relat_1(sK0,sK1),X7),k9_relat_1(k7_relat_1(sK0,sK2),X7))) )),
% 3.29/0.77    inference(superposition,[],[f3615,f171])).
% 3.29/0.77  fof(f171,plain,(
% 3.29/0.77    k7_relat_1(sK0,sK1) = k7_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 3.29/0.77    inference(subsumption_resolution,[],[f164,f62])).
% 3.29/0.77  fof(f164,plain,(
% 3.29/0.77    k7_relat_1(sK0,sK1) = k7_relat_1(k7_relat_1(sK0,sK1),sK2) | ~v1_relat_1(k7_relat_1(sK0,sK1))),
% 3.29/0.77    inference(resolution,[],[f141,f51])).
% 3.29/0.77  fof(f141,plain,(
% 3.29/0.77    r1_tarski(k1_relat_1(k7_relat_1(sK0,sK1)),sK2)),
% 3.29/0.77    inference(resolution,[],[f74,f63])).
% 3.29/0.77  fof(f74,plain,(
% 3.29/0.77    ( ! [X1] : (~r1_tarski(X1,sK1) | r1_tarski(X1,sK2)) )),
% 3.29/0.77    inference(resolution,[],[f38,f57])).
% 3.29/0.77  fof(f57,plain,(
% 3.29/0.77    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.29/0.77    inference(cnf_transformation,[],[f31])).
% 3.29/0.77  fof(f31,plain,(
% 3.29/0.77    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.29/0.77    inference(flattening,[],[f30])).
% 3.29/0.77  fof(f30,plain,(
% 3.29/0.77    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.29/0.77    inference(ennf_transformation,[],[f2])).
% 3.29/0.77  fof(f2,axiom,(
% 3.29/0.77    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.29/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 3.29/0.77  fof(f38,plain,(
% 3.29/0.77    r1_tarski(sK1,sK2)),
% 3.29/0.77    inference(cnf_transformation,[],[f34])).
% 3.29/0.77  fof(f3615,plain,(
% 3.29/0.77    ( ! [X4,X2,X3] : (r1_tarski(k9_relat_1(k7_relat_1(k7_relat_1(sK0,X4),X2),X3),k9_relat_1(k7_relat_1(sK0,X2),X3))) )),
% 3.29/0.77    inference(backward_demodulation,[],[f1015,f594])).
% 3.29/0.77  fof(f594,plain,(
% 3.29/0.77    ( ! [X6,X4,X5] : (k9_relat_1(k7_relat_1(sK0,X5),k9_relat_1(k6_relat_1(X4),X6)) = k9_relat_1(k7_relat_1(k7_relat_1(sK0,X5),X4),X6)) )),
% 3.29/0.77    inference(subsumption_resolution,[],[f593,f40])).
% 3.29/0.77  fof(f40,plain,(
% 3.29/0.77    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 3.29/0.77    inference(cnf_transformation,[],[f3])).
% 3.29/0.77  fof(f3,axiom,(
% 3.29/0.77    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 3.29/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 3.29/0.77  fof(f593,plain,(
% 3.29/0.77    ( ! [X6,X4,X5] : (k9_relat_1(k7_relat_1(sK0,X5),k9_relat_1(k6_relat_1(X4),X6)) = k9_relat_1(k7_relat_1(k7_relat_1(sK0,X5),X4),X6) | ~v1_relat_1(k6_relat_1(X4))) )),
% 3.29/0.77    inference(subsumption_resolution,[],[f592,f62])).
% 3.29/0.77  fof(f592,plain,(
% 3.29/0.77    ( ! [X6,X4,X5] : (k9_relat_1(k7_relat_1(sK0,X5),k9_relat_1(k6_relat_1(X4),X6)) = k9_relat_1(k7_relat_1(k7_relat_1(sK0,X5),X4),X6) | ~v1_relat_1(k7_relat_1(sK0,X5)) | ~v1_relat_1(k6_relat_1(X4))) )),
% 3.29/0.77    inference(superposition,[],[f52,f82])).
% 3.29/0.77  fof(f82,plain,(
% 3.29/0.77    ( ! [X6,X7] : (k7_relat_1(k7_relat_1(sK0,X6),X7) = k5_relat_1(k6_relat_1(X7),k7_relat_1(sK0,X6))) )),
% 3.29/0.77    inference(resolution,[],[f62,f47])).
% 3.29/0.77  fof(f52,plain,(
% 3.29/0.77    ( ! [X2,X0,X1] : (k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 3.29/0.77    inference(cnf_transformation,[],[f27])).
% 3.29/0.77  fof(f27,plain,(
% 3.29/0.77    ! [X0,X1] : (! [X2] : (k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 3.29/0.77    inference(ennf_transformation,[],[f8])).
% 3.29/0.77  fof(f8,axiom,(
% 3.29/0.77    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k9_relat_1(k5_relat_1(X1,X2),X0) = k9_relat_1(X2,k9_relat_1(X1,X0))))),
% 3.29/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t159_relat_1)).
% 3.29/0.77  fof(f1015,plain,(
% 3.29/0.77    ( ! [X4,X2,X3] : (r1_tarski(k9_relat_1(k7_relat_1(sK0,X4),k9_relat_1(k6_relat_1(X2),X3)),k9_relat_1(k7_relat_1(sK0,X2),X3))) )),
% 3.29/0.77    inference(superposition,[],[f304,f183])).
% 3.29/0.77  fof(f183,plain,(
% 3.29/0.77    ( ! [X2,X3] : (k9_relat_1(sK0,k9_relat_1(k6_relat_1(X2),X3)) = k9_relat_1(k7_relat_1(sK0,X2),X3)) )),
% 3.29/0.77    inference(subsumption_resolution,[],[f182,f40])).
% 3.29/0.77  fof(f182,plain,(
% 3.29/0.77    ( ! [X2,X3] : (k9_relat_1(sK0,k9_relat_1(k6_relat_1(X2),X3)) = k9_relat_1(k7_relat_1(sK0,X2),X3) | ~v1_relat_1(k6_relat_1(X2))) )),
% 3.29/0.77    inference(subsumption_resolution,[],[f181,f37])).
% 3.29/0.77  fof(f181,plain,(
% 3.29/0.77    ( ! [X2,X3] : (k9_relat_1(sK0,k9_relat_1(k6_relat_1(X2),X3)) = k9_relat_1(k7_relat_1(sK0,X2),X3) | ~v1_relat_1(sK0) | ~v1_relat_1(k6_relat_1(X2))) )),
% 3.29/0.77    inference(superposition,[],[f52,f64])).
% 3.29/0.77  fof(f64,plain,(
% 3.29/0.77    ( ! [X2] : (k7_relat_1(sK0,X2) = k5_relat_1(k6_relat_1(X2),sK0)) )),
% 3.29/0.77    inference(resolution,[],[f37,f47])).
% 3.29/0.77  % SZS output end Proof for theBenchmark
% 3.29/0.77  % (24535)------------------------------
% 3.29/0.77  % (24535)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.29/0.77  % (24535)Termination reason: Refutation
% 3.29/0.77  
% 3.29/0.77  % (24535)Memory used [KB]: 3198
% 3.29/0.77  % (24535)Time elapsed: 0.357 s
% 3.29/0.77  % (24535)------------------------------
% 3.29/0.77  % (24535)------------------------------
% 3.29/0.78  % (24526)Success in time 0.421 s
%------------------------------------------------------------------------------
