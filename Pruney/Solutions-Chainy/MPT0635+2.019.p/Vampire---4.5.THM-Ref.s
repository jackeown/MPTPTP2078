%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:21 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 330 expanded)
%              Number of leaves         :   21 ( 105 expanded)
%              Depth                    :   25
%              Number of atoms          :  183 ( 476 expanded)
%              Number of equality atoms :   89 ( 313 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1168,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1167,f127])).

fof(f127,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(trivial_inequality_removal,[],[f126])).

fof(f126,plain,
    ( k1_funct_1(sK2,sK0) != k1_funct_1(sK2,sK0)
    | ~ r2_hidden(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f125])).

fof(f125,plain,
    ( k1_funct_1(sK2,sK0) != k1_funct_1(sK2,sK0)
    | ~ r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(superposition,[],[f124,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k6_relat_1(X1),X0) = X0
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k6_relat_1(X1),X0) = X0
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_funct_1(k6_relat_1(X1),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_1)).

fof(f124,plain,
    ( k1_funct_1(sK2,sK0) != k1_funct_1(sK2,k1_funct_1(k6_relat_1(sK1),sK0))
    | ~ r2_hidden(sK0,sK1) ),
    inference(forward_demodulation,[],[f123,f44])).

fof(f44,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f123,plain,
    ( k1_funct_1(sK2,sK0) != k1_funct_1(sK2,k1_funct_1(k6_relat_1(sK1),sK0))
    | ~ r2_hidden(sK0,k1_relat_1(k6_relat_1(sK1))) ),
    inference(subsumption_resolution,[],[f122,f40])).

fof(f40,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f122,plain,
    ( k1_funct_1(sK2,sK0) != k1_funct_1(sK2,k1_funct_1(k6_relat_1(sK1),sK0))
    | ~ r2_hidden(sK0,k1_relat_1(k6_relat_1(sK1)))
    | ~ v1_relat_1(k6_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f121,f43])).

fof(f43,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f121,plain,
    ( k1_funct_1(sK2,sK0) != k1_funct_1(sK2,k1_funct_1(k6_relat_1(sK1),sK0))
    | ~ r2_hidden(sK0,k1_relat_1(k6_relat_1(sK1)))
    | ~ v1_funct_1(k6_relat_1(sK1))
    | ~ v1_relat_1(k6_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f120,f36])).

fof(f36,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( k1_funct_1(sK2,sK0) != k1_funct_1(k5_relat_1(k6_relat_1(sK1),sK2),sK0)
    & r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f31])).

fof(f31,plain,
    ( ? [X0,X1,X2] :
        ( k1_funct_1(X2,X0) != k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)
        & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k1_funct_1(sK2,sK0) != k1_funct_1(k5_relat_1(k6_relat_1(sK1),sK2),sK0)
      & r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)
      & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)
      & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
         => k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))
       => k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_1)).

fof(f120,plain,
    ( k1_funct_1(sK2,sK0) != k1_funct_1(sK2,k1_funct_1(k6_relat_1(sK1),sK0))
    | ~ r2_hidden(sK0,k1_relat_1(k6_relat_1(sK1)))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(k6_relat_1(sK1))
    | ~ v1_relat_1(k6_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f115,f37])).

fof(f37,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f115,plain,
    ( k1_funct_1(sK2,sK0) != k1_funct_1(sK2,k1_funct_1(k6_relat_1(sK1),sK0))
    | ~ r2_hidden(sK0,k1_relat_1(k6_relat_1(sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(k6_relat_1(sK1))
    | ~ v1_relat_1(k6_relat_1(sK1)) ),
    inference(superposition,[],[f39,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

fof(f39,plain,(
    k1_funct_1(sK2,sK0) != k1_funct_1(k5_relat_1(k6_relat_1(sK1),sK2),sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f1167,plain,(
    r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f1166,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f1166,plain,(
    r1_tarski(k1_tarski(sK0),sK1) ),
    inference(resolution,[],[f1164,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(resolution,[],[f55,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_xboole_0(X1,X2))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

fof(f1164,plain,(
    r2_hidden(sK0,k3_xboole_0(sK1,k1_relat_1(sK2))) ),
    inference(backward_demodulation,[],[f38,f1161])).

fof(f1161,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2) ),
    inference(superposition,[],[f988,f47])).

fof(f47,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f988,plain,(
    ! [X4,X3] : k3_xboole_0(X3,X4) = k1_setfam_1(k2_tarski(X4,X3)) ),
    inference(superposition,[],[f47,f946])).

fof(f946,plain,(
    ! [X2,X3] : k2_tarski(X2,X3) = k2_tarski(X3,X2) ),
    inference(superposition,[],[f928,f48])).

fof(f48,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f928,plain,(
    ! [X6,X7] : k1_enumset1(X6,X6,X7) = k2_tarski(X7,X6) ),
    inference(forward_demodulation,[],[f912,f190])).

fof(f190,plain,(
    ! [X6,X7] : k2_enumset1(X7,X6,X6,X6) = k2_tarski(X6,X7) ),
    inference(superposition,[],[f180,f150])).

fof(f150,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X1,X1,X2) = k2_enumset1(X1,X0,X0,X2) ),
    inference(superposition,[],[f113,f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f113,plain,(
    ! [X14,X17,X15,X16] : k3_enumset1(X14,X15,X16,X16,X17) = k2_enumset1(X16,X15,X14,X17) ),
    inference(forward_demodulation,[],[f111,f112])).

fof(f112,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(forward_demodulation,[],[f108,f60])).

fof(f108,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(superposition,[],[f98,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f98,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(forward_demodulation,[],[f97,f61])).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f97,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(superposition,[],[f63,f60])).

fof(f63,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).

fof(f111,plain,(
    ! [X14,X17,X15,X16] : k3_enumset1(X14,X15,X16,X16,X17) = k2_xboole_0(k1_enumset1(X16,X15,X14),k1_tarski(X17)) ),
    inference(superposition,[],[f98,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X2,X1,X0,X0) ),
    inference(superposition,[],[f59,f54])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).

fof(f180,plain,(
    ! [X8,X9] : k2_enumset1(X9,X8,X8,X9) = k2_tarski(X9,X8) ),
    inference(forward_demodulation,[],[f166,f48])).

fof(f166,plain,(
    ! [X8,X9] : k1_enumset1(X9,X9,X8) = k2_enumset1(X9,X8,X8,X9) ),
    inference(superposition,[],[f150,f86])).

fof(f912,plain,(
    ! [X6,X7] : k1_enumset1(X6,X6,X7) = k2_enumset1(X6,X7,X7,X7) ),
    inference(superposition,[],[f695,f60])).

fof(f695,plain,(
    ! [X14,X12,X13] : k3_enumset1(X13,X14,X12,X12,X12) = k1_enumset1(X13,X14,X12) ),
    inference(forward_demodulation,[],[f689,f187])).

fof(f187,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(forward_demodulation,[],[f184,f54])).

fof(f184,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(superposition,[],[f112,f48])).

fof(f689,plain,(
    ! [X14,X12,X13] : k3_enumset1(X13,X14,X12,X12,X12) = k2_xboole_0(k2_tarski(X13,X14),k1_tarski(X12)) ),
    inference(superposition,[],[f257,f642])).

fof(f642,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(forward_demodulation,[],[f641,f263])).

fof(f263,plain,(
    ! [X2] : k1_tarski(X2) = k3_tarski(k1_tarski(k1_tarski(X2))) ),
    inference(forward_demodulation,[],[f261,f41])).

fof(f41,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f261,plain,(
    ! [X2] : k3_tarski(k1_tarski(k1_tarski(X2))) = k2_tarski(X2,X2) ),
    inference(superposition,[],[f248,f67])).

fof(f67,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = k3_tarski(k1_tarski(X0)) ),
    inference(superposition,[],[f46,f41])).

fof(f46,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f248,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(forward_demodulation,[],[f247,f48])).

fof(f247,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(superposition,[],[f187,f41])).

fof(f641,plain,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k3_tarski(k1_tarski(k1_tarski(X0))) ),
    inference(forward_demodulation,[],[f624,f41])).

fof(f624,plain,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k3_tarski(k1_tarski(k2_tarski(X0,X0))) ),
    inference(superposition,[],[f613,f198])).

fof(f198,plain,(
    ! [X6,X8,X7] : k3_enumset1(X6,X7,X7,X6,X8) = k1_enumset1(X6,X7,X8) ),
    inference(forward_demodulation,[],[f194,f187])).

fof(f194,plain,(
    ! [X6,X8,X7] : k3_enumset1(X6,X7,X7,X6,X8) = k2_xboole_0(k2_tarski(X6,X7),k1_tarski(X8)) ),
    inference(superposition,[],[f98,f180])).

fof(f613,plain,(
    ! [X0,X1] : k3_enumset1(X0,X1,X0,X0,X1) = k3_tarski(k1_tarski(k2_tarski(X0,X1))) ),
    inference(forward_demodulation,[],[f609,f48])).

fof(f609,plain,(
    ! [X0,X1] : k3_enumset1(X0,X1,X0,X0,X1) = k3_tarski(k1_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(superposition,[],[f255,f61])).

fof(f255,plain,(
    ! [X6,X8,X7] : k3_tarski(k1_tarski(k1_enumset1(X6,X7,X8))) = k4_enumset1(X6,X7,X8,X6,X7,X8) ),
    inference(superposition,[],[f135,f67])).

fof(f135,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(forward_demodulation,[],[f128,f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f128,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(superposition,[],[f107,f54])).

fof(f107,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    inference(forward_demodulation,[],[f103,f64])).

fof(f64,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f103,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    inference(superposition,[],[f65,f60])).

fof(f65,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_enumset1)).

fof(f257,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    inference(forward_demodulation,[],[f249,f61])).

fof(f249,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    inference(superposition,[],[f135,f48])).

fof(f38,plain,(
    r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1)) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:17:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.44  % (26331)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.19/0.45  % (26344)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.19/0.46  % (26336)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.19/0.49  % (26332)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.19/0.49  % (26330)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.19/0.49  % (26331)Refutation found. Thanks to Tanya!
% 0.19/0.49  % SZS status Theorem for theBenchmark
% 0.19/0.49  % SZS output start Proof for theBenchmark
% 0.19/0.49  fof(f1168,plain,(
% 0.19/0.49    $false),
% 0.19/0.49    inference(subsumption_resolution,[],[f1167,f127])).
% 0.19/0.49  fof(f127,plain,(
% 0.19/0.49    ~r2_hidden(sK0,sK1)),
% 0.19/0.49    inference(trivial_inequality_removal,[],[f126])).
% 0.19/0.49  fof(f126,plain,(
% 0.19/0.49    k1_funct_1(sK2,sK0) != k1_funct_1(sK2,sK0) | ~r2_hidden(sK0,sK1)),
% 0.19/0.49    inference(duplicate_literal_removal,[],[f125])).
% 0.19/0.49  fof(f125,plain,(
% 0.19/0.49    k1_funct_1(sK2,sK0) != k1_funct_1(sK2,sK0) | ~r2_hidden(sK0,sK1) | ~r2_hidden(sK0,sK1)),
% 0.19/0.49    inference(superposition,[],[f124,f50])).
% 0.19/0.49  fof(f50,plain,(
% 0.19/0.49    ( ! [X0,X1] : (k1_funct_1(k6_relat_1(X1),X0) = X0 | ~r2_hidden(X0,X1)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f27])).
% 0.19/0.49  fof(f27,plain,(
% 0.19/0.49    ! [X0,X1] : (k1_funct_1(k6_relat_1(X1),X0) = X0 | ~r2_hidden(X0,X1))),
% 0.19/0.49    inference(ennf_transformation,[],[f21])).
% 0.19/0.49  fof(f21,axiom,(
% 0.19/0.49    ! [X0,X1] : (r2_hidden(X0,X1) => k1_funct_1(k6_relat_1(X1),X0) = X0)),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_1)).
% 0.19/0.49  fof(f124,plain,(
% 0.19/0.49    k1_funct_1(sK2,sK0) != k1_funct_1(sK2,k1_funct_1(k6_relat_1(sK1),sK0)) | ~r2_hidden(sK0,sK1)),
% 0.19/0.49    inference(forward_demodulation,[],[f123,f44])).
% 0.19/0.49  fof(f44,plain,(
% 0.19/0.49    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.19/0.49    inference(cnf_transformation,[],[f17])).
% 0.19/0.50  fof(f17,axiom,(
% 0.19/0.50    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.19/0.50  fof(f123,plain,(
% 0.19/0.50    k1_funct_1(sK2,sK0) != k1_funct_1(sK2,k1_funct_1(k6_relat_1(sK1),sK0)) | ~r2_hidden(sK0,k1_relat_1(k6_relat_1(sK1)))),
% 0.19/0.50    inference(subsumption_resolution,[],[f122,f40])).
% 0.19/0.50  fof(f40,plain,(
% 0.19/0.50    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.19/0.50    inference(cnf_transformation,[],[f16])).
% 0.19/0.50  fof(f16,axiom,(
% 0.19/0.50    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.19/0.50  fof(f122,plain,(
% 0.19/0.50    k1_funct_1(sK2,sK0) != k1_funct_1(sK2,k1_funct_1(k6_relat_1(sK1),sK0)) | ~r2_hidden(sK0,k1_relat_1(k6_relat_1(sK1))) | ~v1_relat_1(k6_relat_1(sK1))),
% 0.19/0.50    inference(subsumption_resolution,[],[f121,f43])).
% 0.19/0.50  fof(f43,plain,(
% 0.19/0.50    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.19/0.50    inference(cnf_transformation,[],[f19])).
% 0.19/0.50  fof(f19,axiom,(
% 0.19/0.50    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.19/0.50  fof(f121,plain,(
% 0.19/0.50    k1_funct_1(sK2,sK0) != k1_funct_1(sK2,k1_funct_1(k6_relat_1(sK1),sK0)) | ~r2_hidden(sK0,k1_relat_1(k6_relat_1(sK1))) | ~v1_funct_1(k6_relat_1(sK1)) | ~v1_relat_1(k6_relat_1(sK1))),
% 0.19/0.50    inference(subsumption_resolution,[],[f120,f36])).
% 0.19/0.50  fof(f36,plain,(
% 0.19/0.50    v1_relat_1(sK2)),
% 0.19/0.50    inference(cnf_transformation,[],[f32])).
% 0.19/0.50  fof(f32,plain,(
% 0.19/0.50    k1_funct_1(sK2,sK0) != k1_funct_1(k5_relat_1(k6_relat_1(sK1),sK2),sK0) & r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.19/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f31])).
% 0.19/0.50  fof(f31,plain,(
% 0.19/0.50    ? [X0,X1,X2] : (k1_funct_1(X2,X0) != k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (k1_funct_1(sK2,sK0) != k1_funct_1(k5_relat_1(k6_relat_1(sK1),sK2),sK0) & r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.19/0.50    introduced(choice_axiom,[])).
% 0.19/0.50  fof(f25,plain,(
% 0.19/0.50    ? [X0,X1,X2] : (k1_funct_1(X2,X0) != k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.19/0.50    inference(flattening,[],[f24])).
% 0.19/0.50  fof(f24,plain,(
% 0.19/0.50    ? [X0,X1,X2] : ((k1_funct_1(X2,X0) != k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0) & r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.19/0.50    inference(ennf_transformation,[],[f23])).
% 0.19/0.50  fof(f23,negated_conjecture,(
% 0.19/0.50    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) => k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)))),
% 0.19/0.50    inference(negated_conjecture,[],[f22])).
% 0.19/0.50  fof(f22,conjecture,(
% 0.19/0.50    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k3_xboole_0(k1_relat_1(X2),X1)) => k1_funct_1(X2,X0) = k1_funct_1(k5_relat_1(k6_relat_1(X1),X2),X0)))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_1)).
% 0.19/0.50  fof(f120,plain,(
% 0.19/0.50    k1_funct_1(sK2,sK0) != k1_funct_1(sK2,k1_funct_1(k6_relat_1(sK1),sK0)) | ~r2_hidden(sK0,k1_relat_1(k6_relat_1(sK1))) | ~v1_relat_1(sK2) | ~v1_funct_1(k6_relat_1(sK1)) | ~v1_relat_1(k6_relat_1(sK1))),
% 0.19/0.50    inference(subsumption_resolution,[],[f115,f37])).
% 0.19/0.50  fof(f37,plain,(
% 0.19/0.50    v1_funct_1(sK2)),
% 0.19/0.50    inference(cnf_transformation,[],[f32])).
% 0.19/0.50  fof(f115,plain,(
% 0.19/0.50    k1_funct_1(sK2,sK0) != k1_funct_1(sK2,k1_funct_1(k6_relat_1(sK1),sK0)) | ~r2_hidden(sK0,k1_relat_1(k6_relat_1(sK1))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(k6_relat_1(sK1)) | ~v1_relat_1(k6_relat_1(sK1))),
% 0.19/0.50    inference(superposition,[],[f39,f51])).
% 0.19/0.50  fof(f51,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f29])).
% 0.19/0.50  fof(f29,plain,(
% 0.19/0.50    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.19/0.50    inference(flattening,[],[f28])).
% 0.19/0.50  fof(f28,plain,(
% 0.19/0.50    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.19/0.50    inference(ennf_transformation,[],[f20])).
% 0.19/0.50  fof(f20,axiom,(
% 0.19/0.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)))))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).
% 0.19/0.50  fof(f39,plain,(
% 0.19/0.50    k1_funct_1(sK2,sK0) != k1_funct_1(k5_relat_1(k6_relat_1(sK1),sK2),sK0)),
% 0.19/0.50    inference(cnf_transformation,[],[f32])).
% 0.19/0.50  fof(f1167,plain,(
% 0.19/0.50    r2_hidden(sK0,sK1)),
% 0.19/0.50    inference(resolution,[],[f1166,f52])).
% 0.19/0.50  fof(f52,plain,(
% 0.19/0.50    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f33])).
% 0.19/0.50  fof(f33,plain,(
% 0.19/0.50    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.19/0.50    inference(nnf_transformation,[],[f12])).
% 0.19/0.50  fof(f12,axiom,(
% 0.19/0.50    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.19/0.50  fof(f1166,plain,(
% 0.19/0.50    r1_tarski(k1_tarski(sK0),sK1)),
% 0.19/0.50    inference(resolution,[],[f1164,f69])).
% 0.19/0.50  fof(f69,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_xboole_0(X1,X2)) | r1_tarski(k1_tarski(X0),X1)) )),
% 0.19/0.50    inference(resolution,[],[f55,f53])).
% 0.19/0.50  fof(f53,plain,(
% 0.19/0.50    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f33])).
% 0.19/0.50  fof(f55,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_xboole_0(X1,X2)) | r1_tarski(X0,X1)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f30])).
% 0.19/0.50  fof(f30,plain,(
% 0.19/0.50    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.19/0.50    inference(ennf_transformation,[],[f1])).
% 0.19/0.50  fof(f1,axiom,(
% 0.19/0.50    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).
% 0.19/0.50  fof(f1164,plain,(
% 0.19/0.50    r2_hidden(sK0,k3_xboole_0(sK1,k1_relat_1(sK2)))),
% 0.19/0.50    inference(backward_demodulation,[],[f38,f1161])).
% 0.19/0.50  fof(f1161,plain,(
% 0.19/0.50    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)) )),
% 0.19/0.50    inference(superposition,[],[f988,f47])).
% 0.19/0.50  fof(f47,plain,(
% 0.19/0.50    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f15])).
% 0.19/0.50  fof(f15,axiom,(
% 0.19/0.50    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.19/0.50  fof(f988,plain,(
% 0.19/0.50    ( ! [X4,X3] : (k3_xboole_0(X3,X4) = k1_setfam_1(k2_tarski(X4,X3))) )),
% 0.19/0.50    inference(superposition,[],[f47,f946])).
% 0.19/0.50  fof(f946,plain,(
% 0.19/0.50    ( ! [X2,X3] : (k2_tarski(X2,X3) = k2_tarski(X3,X2)) )),
% 0.19/0.50    inference(superposition,[],[f928,f48])).
% 0.19/0.50  fof(f48,plain,(
% 0.19/0.50    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f6])).
% 0.19/0.50  fof(f6,axiom,(
% 0.19/0.50    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.19/0.50  fof(f928,plain,(
% 0.19/0.50    ( ! [X6,X7] : (k1_enumset1(X6,X6,X7) = k2_tarski(X7,X6)) )),
% 0.19/0.50    inference(forward_demodulation,[],[f912,f190])).
% 0.19/0.50  fof(f190,plain,(
% 0.19/0.50    ( ! [X6,X7] : (k2_enumset1(X7,X6,X6,X6) = k2_tarski(X6,X7)) )),
% 0.19/0.50    inference(superposition,[],[f180,f150])).
% 0.19/0.50  fof(f150,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (k2_enumset1(X0,X1,X1,X2) = k2_enumset1(X1,X0,X0,X2)) )),
% 0.19/0.50    inference(superposition,[],[f113,f60])).
% 0.19/0.50  fof(f60,plain,(
% 0.19/0.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f8])).
% 0.19/0.50  fof(f8,axiom,(
% 0.19/0.50    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.19/0.50  fof(f113,plain,(
% 0.19/0.50    ( ! [X14,X17,X15,X16] : (k3_enumset1(X14,X15,X16,X16,X17) = k2_enumset1(X16,X15,X14,X17)) )),
% 0.19/0.50    inference(forward_demodulation,[],[f111,f112])).
% 0.19/0.50  fof(f112,plain,(
% 0.19/0.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 0.19/0.50    inference(forward_demodulation,[],[f108,f60])).
% 0.19/0.50  fof(f108,plain,(
% 0.19/0.50    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 0.19/0.50    inference(superposition,[],[f98,f54])).
% 0.19/0.50  fof(f54,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f7])).
% 0.19/0.50  fof(f7,axiom,(
% 0.19/0.50    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.19/0.50  fof(f98,plain,(
% 0.19/0.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 0.19/0.50    inference(forward_demodulation,[],[f97,f61])).
% 0.19/0.50  fof(f61,plain,(
% 0.19/0.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f9])).
% 0.19/0.50  fof(f9,axiom,(
% 0.19/0.50    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.19/0.50  fof(f97,plain,(
% 0.19/0.50    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 0.19/0.50    inference(superposition,[],[f63,f60])).
% 0.19/0.50  fof(f63,plain,(
% 0.19/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))) )),
% 0.19/0.50    inference(cnf_transformation,[],[f3])).
% 0.19/0.50  fof(f3,axiom,(
% 0.19/0.50    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).
% 0.19/0.50  fof(f111,plain,(
% 0.19/0.50    ( ! [X14,X17,X15,X16] : (k3_enumset1(X14,X15,X16,X16,X17) = k2_xboole_0(k1_enumset1(X16,X15,X14),k1_tarski(X17))) )),
% 0.19/0.50    inference(superposition,[],[f98,f86])).
% 0.19/0.50  fof(f86,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X2,X1,X0,X0)) )),
% 0.19/0.50    inference(superposition,[],[f59,f54])).
% 0.19/0.50  fof(f59,plain,(
% 0.19/0.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f2])).
% 0.19/0.50  fof(f2,axiom,(
% 0.19/0.50    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).
% 0.19/0.50  fof(f180,plain,(
% 0.19/0.50    ( ! [X8,X9] : (k2_enumset1(X9,X8,X8,X9) = k2_tarski(X9,X8)) )),
% 0.19/0.50    inference(forward_demodulation,[],[f166,f48])).
% 0.19/0.50  fof(f166,plain,(
% 0.19/0.50    ( ! [X8,X9] : (k1_enumset1(X9,X9,X8) = k2_enumset1(X9,X8,X8,X9)) )),
% 0.19/0.50    inference(superposition,[],[f150,f86])).
% 0.19/0.50  fof(f912,plain,(
% 0.19/0.50    ( ! [X6,X7] : (k1_enumset1(X6,X6,X7) = k2_enumset1(X6,X7,X7,X7)) )),
% 0.19/0.50    inference(superposition,[],[f695,f60])).
% 0.19/0.50  fof(f695,plain,(
% 0.19/0.50    ( ! [X14,X12,X13] : (k3_enumset1(X13,X14,X12,X12,X12) = k1_enumset1(X13,X14,X12)) )),
% 0.19/0.50    inference(forward_demodulation,[],[f689,f187])).
% 0.19/0.50  fof(f187,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 0.19/0.50    inference(forward_demodulation,[],[f184,f54])).
% 0.19/0.50  fof(f184,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 0.19/0.50    inference(superposition,[],[f112,f48])).
% 0.19/0.50  fof(f689,plain,(
% 0.19/0.50    ( ! [X14,X12,X13] : (k3_enumset1(X13,X14,X12,X12,X12) = k2_xboole_0(k2_tarski(X13,X14),k1_tarski(X12))) )),
% 0.19/0.50    inference(superposition,[],[f257,f642])).
% 0.19/0.50  fof(f642,plain,(
% 0.19/0.50    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.19/0.50    inference(forward_demodulation,[],[f641,f263])).
% 0.19/0.50  fof(f263,plain,(
% 0.19/0.50    ( ! [X2] : (k1_tarski(X2) = k3_tarski(k1_tarski(k1_tarski(X2)))) )),
% 0.19/0.50    inference(forward_demodulation,[],[f261,f41])).
% 0.19/0.50  fof(f41,plain,(
% 0.19/0.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f5])).
% 0.19/0.50  fof(f5,axiom,(
% 0.19/0.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.19/0.50  fof(f261,plain,(
% 0.19/0.50    ( ! [X2] : (k3_tarski(k1_tarski(k1_tarski(X2))) = k2_tarski(X2,X2)) )),
% 0.19/0.50    inference(superposition,[],[f248,f67])).
% 0.19/0.50  fof(f67,plain,(
% 0.19/0.50    ( ! [X0] : (k2_xboole_0(X0,X0) = k3_tarski(k1_tarski(X0))) )),
% 0.19/0.50    inference(superposition,[],[f46,f41])).
% 0.19/0.50  fof(f46,plain,(
% 0.19/0.50    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f13])).
% 0.19/0.50  fof(f13,axiom,(
% 0.19/0.50    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.19/0.50  fof(f248,plain,(
% 0.19/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.19/0.50    inference(forward_demodulation,[],[f247,f48])).
% 0.19/0.50  fof(f247,plain,(
% 0.19/0.50    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.19/0.50    inference(superposition,[],[f187,f41])).
% 0.19/0.50  fof(f641,plain,(
% 0.19/0.50    ( ! [X0] : (k1_enumset1(X0,X0,X0) = k3_tarski(k1_tarski(k1_tarski(X0)))) )),
% 0.19/0.50    inference(forward_demodulation,[],[f624,f41])).
% 0.19/0.50  fof(f624,plain,(
% 0.19/0.50    ( ! [X0] : (k1_enumset1(X0,X0,X0) = k3_tarski(k1_tarski(k2_tarski(X0,X0)))) )),
% 0.19/0.50    inference(superposition,[],[f613,f198])).
% 0.19/0.50  fof(f198,plain,(
% 0.19/0.50    ( ! [X6,X8,X7] : (k3_enumset1(X6,X7,X7,X6,X8) = k1_enumset1(X6,X7,X8)) )),
% 0.19/0.50    inference(forward_demodulation,[],[f194,f187])).
% 0.19/0.50  fof(f194,plain,(
% 0.19/0.50    ( ! [X6,X8,X7] : (k3_enumset1(X6,X7,X7,X6,X8) = k2_xboole_0(k2_tarski(X6,X7),k1_tarski(X8))) )),
% 0.19/0.50    inference(superposition,[],[f98,f180])).
% 0.19/0.50  fof(f613,plain,(
% 0.19/0.50    ( ! [X0,X1] : (k3_enumset1(X0,X1,X0,X0,X1) = k3_tarski(k1_tarski(k2_tarski(X0,X1)))) )),
% 0.19/0.50    inference(forward_demodulation,[],[f609,f48])).
% 0.19/0.50  fof(f609,plain,(
% 0.19/0.50    ( ! [X0,X1] : (k3_enumset1(X0,X1,X0,X0,X1) = k3_tarski(k1_tarski(k1_enumset1(X0,X0,X1)))) )),
% 0.19/0.50    inference(superposition,[],[f255,f61])).
% 0.19/0.50  fof(f255,plain,(
% 0.19/0.50    ( ! [X6,X8,X7] : (k3_tarski(k1_tarski(k1_enumset1(X6,X7,X8))) = k4_enumset1(X6,X7,X8,X6,X7,X8)) )),
% 0.19/0.50    inference(superposition,[],[f135,f67])).
% 0.19/0.50  fof(f135,plain,(
% 0.19/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))) )),
% 0.19/0.50    inference(forward_demodulation,[],[f128,f62])).
% 0.19/0.50  fof(f62,plain,(
% 0.19/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f10])).
% 0.19/0.50  fof(f10,axiom,(
% 0.19/0.50    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.19/0.50  fof(f128,plain,(
% 0.19/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))) )),
% 0.19/0.50    inference(superposition,[],[f107,f54])).
% 0.19/0.50  fof(f107,plain,(
% 0.19/0.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6))) )),
% 0.19/0.50    inference(forward_demodulation,[],[f103,f64])).
% 0.19/0.50  fof(f64,plain,(
% 0.19/0.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f11])).
% 0.19/0.50  fof(f11,axiom,(
% 0.19/0.50    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.19/0.50  fof(f103,plain,(
% 0.19/0.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6))) )),
% 0.19/0.50    inference(superposition,[],[f65,f60])).
% 0.19/0.50  fof(f65,plain,(
% 0.19/0.50    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7))) )),
% 0.19/0.50    inference(cnf_transformation,[],[f4])).
% 0.19/0.50  fof(f4,axiom,(
% 0.19/0.50    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_enumset1)).
% 0.19/0.50  fof(f257,plain,(
% 0.19/0.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))) )),
% 0.19/0.50    inference(forward_demodulation,[],[f249,f61])).
% 0.19/0.50  fof(f249,plain,(
% 0.19/0.50    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))) )),
% 0.19/0.50    inference(superposition,[],[f135,f48])).
% 0.19/0.50  fof(f38,plain,(
% 0.19/0.50    r2_hidden(sK0,k3_xboole_0(k1_relat_1(sK2),sK1))),
% 0.19/0.50    inference(cnf_transformation,[],[f32])).
% 0.19/0.50  % SZS output end Proof for theBenchmark
% 0.19/0.50  % (26331)------------------------------
% 0.19/0.50  % (26331)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (26331)Termination reason: Refutation
% 0.19/0.50  
% 0.19/0.50  % (26331)Memory used [KB]: 2814
% 0.19/0.50  % (26331)Time elapsed: 0.061 s
% 0.19/0.50  % (26331)------------------------------
% 0.19/0.50  % (26331)------------------------------
% 0.19/0.50  % (26327)Success in time 0.151 s
%------------------------------------------------------------------------------
