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
% DateTime   : Thu Dec  3 12:50:55 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :   75 (  81 expanded)
%              Number of leaves         :   19 (  22 expanded)
%              Depth                    :   15
%              Number of atoms          :  339 ( 361 expanded)
%              Number of equality atoms :  231 ( 245 expanded)
%              Maximal formula depth    :   23 (   7 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f199,plain,(
    $false ),
    inference(resolution,[],[f196,f131])).

fof(f131,plain,(
    ~ r1_tarski(k3_xboole_0(k1_relat_1(sK2),sK1),k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f128,f83])).

% (13096)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
fof(f83,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f128,plain,
    ( ~ r1_tarski(k3_xboole_0(k1_relat_1(sK2),sK1),k1_relat_1(sK2))
    | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) ),
    inference(resolution,[],[f105,f115])).

fof(f115,plain,(
    ~ r1_tarski(k4_xboole_0(k1_relat_1(sK2),sK1),k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f114,f41])).

fof(f41,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( k6_subset_1(k1_relat_1(sK2),sK1) != k1_relat_1(k7_relat_1(sK2,k6_subset_1(k1_relat_1(sK2),sK1)))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f22,f31])).

fof(f31,plain,
    ( ? [X0,X1] :
        ( k6_subset_1(k1_relat_1(X1),X0) != k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0)))
        & v1_relat_1(X1) )
   => ( k6_subset_1(k1_relat_1(sK2),sK1) != k1_relat_1(k7_relat_1(sK2,k6_subset_1(k1_relat_1(sK2),sK1)))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( k6_subset_1(k1_relat_1(X1),X0) != k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0)))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_relat_1)).

fof(f114,plain,
    ( ~ r1_tarski(k4_xboole_0(k1_relat_1(sK2),sK1),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(trivial_inequality_removal,[],[f113])).

fof(f113,plain,
    ( k4_xboole_0(k1_relat_1(sK2),sK1) != k4_xboole_0(k1_relat_1(sK2),sK1)
    | ~ r1_tarski(k4_xboole_0(k1_relat_1(sK2),sK1),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f94,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f94,plain,(
    k4_xboole_0(k1_relat_1(sK2),sK1) != k1_relat_1(k7_relat_1(sK2,k4_xboole_0(k1_relat_1(sK2),sK1))) ),
    inference(forward_demodulation,[],[f42,f44])).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f42,plain,(
    k6_subset_1(k1_relat_1(sK2),sK1) != k1_relat_1(k7_relat_1(sK2,k6_subset_1(k1_relat_1(sK2),sK1))) ),
    inference(cnf_transformation,[],[f32])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(k3_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,X2) ) ),
    inference(superposition,[],[f55,f48])).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k5_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_xboole_1)).

fof(f196,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(resolution,[],[f193,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_tarski(X0,X1))
      | r1_tarski(k3_xboole_0(X0,X1),X2) ) ),
    inference(superposition,[],[f50,f45])).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

fof(f193,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X0,X1)) ),
    inference(superposition,[],[f179,f47])).

fof(f47,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f179,plain,(
    ! [X12,X13,X11] : r2_hidden(X13,k1_enumset1(X13,X12,X11)) ),
    inference(superposition,[],[f175,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X2,X1,X0,X0) ),
    inference(superposition,[],[f56,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f56,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).

fof(f175,plain,(
    ! [X2,X0,X3,X1] : r2_hidden(X3,k2_enumset1(X0,X1,X2,X3)) ),
    inference(superposition,[],[f169,f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f169,plain,(
    ! [X4,X2,X0,X3,X1] : r2_hidden(X4,k3_enumset1(X0,X1,X2,X3,X4)) ),
    inference(superposition,[],[f164,f58])).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f164,plain,(
    ! [X4,X2,X0,X5,X3,X1] : r2_hidden(X5,k4_enumset1(X0,X1,X2,X3,X4,X5)) ),
    inference(superposition,[],[f161,f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f161,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : r2_hidden(X6,k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) ),
    inference(superposition,[],[f152,f60])).

fof(f60,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f152,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : r2_hidden(X0,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X0)) ),
    inference(resolution,[],[f93,f85])).

fof(f85,plain,(
    ! [X6,X4,X2,X10,X8,X7,X5,X3,X1] :
      ( ~ sP0(X10,X1,X2,X3,X4,X5,X6,X7,X8)
      | r2_hidden(X10,X8) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] :
      ( r2_hidden(X10,X8)
      | X0 != X10
      | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ( ( ( sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X0
              & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X1
              & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X2
              & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X3
              & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X4
              & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X5
              & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X6
              & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X7 )
            | ~ r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) )
          & ( sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X0
            | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X1
            | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X2
            | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X3
            | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X4
            | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X5
            | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X6
            | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X7
            | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) ) ) )
      & ( ! [X10] :
            ( ( r2_hidden(X10,X8)
              | ( X0 != X10
                & X1 != X10
                & X2 != X10
                & X3 != X10
                & X4 != X10
                & X5 != X10
                & X6 != X10
                & X7 != X10 ) )
            & ( X0 = X10
              | X1 = X10
              | X2 = X10
              | X3 = X10
              | X4 = X10
              | X5 = X10
              | X6 = X10
              | X7 = X10
              | ~ r2_hidden(X10,X8) ) )
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f37,f38])).

fof(f38,plain,(
    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X9] :
          ( ( ( X0 != X9
              & X1 != X9
              & X2 != X9
              & X3 != X9
              & X4 != X9
              & X5 != X9
              & X6 != X9
              & X7 != X9 )
            | ~ r2_hidden(X9,X8) )
          & ( X0 = X9
            | X1 = X9
            | X2 = X9
            | X3 = X9
            | X4 = X9
            | X5 = X9
            | X6 = X9
            | X7 = X9
            | r2_hidden(X9,X8) ) )
     => ( ( ( sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X0
            & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X1
            & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X2
            & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X3
            & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X4
            & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X5
            & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X6
            & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X7 )
          | ~ r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) )
        & ( sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X0
          | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X1
          | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X2
          | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X3
          | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X4
          | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X5
          | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X6
          | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X7
          | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) ) ) ) ),
    introduced(choice_axiom,[])).

% (13117)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% (13093)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ? [X9] :
            ( ( ( X0 != X9
                & X1 != X9
                & X2 != X9
                & X3 != X9
                & X4 != X9
                & X5 != X9
                & X6 != X9
                & X7 != X9 )
              | ~ r2_hidden(X9,X8) )
            & ( X0 = X9
              | X1 = X9
              | X2 = X9
              | X3 = X9
              | X4 = X9
              | X5 = X9
              | X6 = X9
              | X7 = X9
              | r2_hidden(X9,X8) ) ) )
      & ( ! [X10] :
            ( ( r2_hidden(X10,X8)
              | ( X0 != X10
                & X1 != X10
                & X2 != X10
                & X3 != X10
                & X4 != X10
                & X5 != X10
                & X6 != X10
                & X7 != X10 ) )
            & ( X0 = X10
              | X1 = X10
              | X2 = X10
              | X3 = X10
              | X4 = X10
              | X5 = X10
              | X6 = X10
              | X7 = X10
              | ~ r2_hidden(X10,X8) ) )
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(rectify,[],[f36])).

% (13119)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
fof(f36,plain,(
    ! [X7,X6,X5,X4,X3,X2,X1,X0,X8] :
      ( ( sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8)
        | ? [X9] :
            ( ( ( X7 != X9
                & X6 != X9
                & X5 != X9
                & X4 != X9
                & X3 != X9
                & X2 != X9
                & X1 != X9
                & X0 != X9 )
              | ~ r2_hidden(X9,X8) )
            & ( X7 = X9
              | X6 = X9
              | X5 = X9
              | X4 = X9
              | X3 = X9
              | X2 = X9
              | X1 = X9
              | X0 = X9
              | r2_hidden(X9,X8) ) ) )
      & ( ! [X9] :
            ( ( r2_hidden(X9,X8)
              | ( X7 != X9
                & X6 != X9
                & X5 != X9
                & X4 != X9
                & X3 != X9
                & X2 != X9
                & X1 != X9
                & X0 != X9 ) )
            & ( X7 = X9
              | X6 = X9
              | X5 = X9
              | X4 = X9
              | X3 = X9
              | X2 = X9
              | X1 = X9
              | X0 = X9
              | ~ r2_hidden(X9,X8) ) )
        | ~ sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8) ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X7,X6,X5,X4,X3,X2,X1,X0,X8] :
      ( ( sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8)
        | ? [X9] :
            ( ( ( X7 != X9
                & X6 != X9
                & X5 != X9
                & X4 != X9
                & X3 != X9
                & X2 != X9
                & X1 != X9
                & X0 != X9 )
              | ~ r2_hidden(X9,X8) )
            & ( X7 = X9
              | X6 = X9
              | X5 = X9
              | X4 = X9
              | X3 = X9
              | X2 = X9
              | X1 = X9
              | X0 = X9
              | r2_hidden(X9,X8) ) ) )
      & ( ! [X9] :
            ( ( r2_hidden(X9,X8)
              | ( X7 != X9
                & X6 != X9
                & X5 != X9
                & X4 != X9
                & X3 != X9
                & X2 != X9
                & X1 != X9
                & X0 != X9 ) )
            & ( X7 = X9
              | X6 = X9
              | X5 = X9
              | X4 = X9
              | X3 = X9
              | X2 = X9
              | X1 = X9
              | X0 = X9
              | ~ r2_hidden(X9,X8) ) )
        | ~ sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X7,X6,X5,X4,X3,X2,X1,X0,X8] :
      ( sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8)
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> ( X7 = X9
            | X6 = X9
            | X5 = X9
            | X4 = X9
            | X3 = X9
            | X2 = X9
            | X1 = X9
            | X0 = X9 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f93,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : sP0(X7,X6,X5,X4,X3,X2,X1,X0,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8)
      | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
        | ~ sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8) )
      & ( sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8)
        | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8) ) ),
    inference(definition_folding,[],[f28,f29])).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> ( X7 = X9
            | X6 = X9
            | X5 = X9
            | X4 = X9
            | X3 = X9
            | X2 = X9
            | X1 = X9
            | X0 = X9 ) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> ~ ( X7 != X9
              & X6 != X9
              & X5 != X9
              & X4 != X9
              & X3 != X9
              & X2 != X9
              & X1 != X9
              & X0 != X9 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:33:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.51  % (13114)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.51  % (13106)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.51  % (13106)Refutation not found, incomplete strategy% (13106)------------------------------
% 0.20/0.51  % (13106)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (13106)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (13106)Memory used [KB]: 1663
% 0.20/0.52  % (13106)Time elapsed: 0.060 s
% 0.20/0.52  % (13106)------------------------------
% 0.20/0.52  % (13106)------------------------------
% 0.20/0.52  % (13097)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (13092)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.52  % (13101)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.53  % (13101)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % (13109)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.31/0.53  % (13095)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.31/0.54  % (13118)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.31/0.54  % SZS output start Proof for theBenchmark
% 1.31/0.54  fof(f199,plain,(
% 1.31/0.54    $false),
% 1.31/0.54    inference(resolution,[],[f196,f131])).
% 1.31/0.54  fof(f131,plain,(
% 1.31/0.54    ~r1_tarski(k3_xboole_0(k1_relat_1(sK2),sK1),k1_relat_1(sK2))),
% 1.31/0.54    inference(subsumption_resolution,[],[f128,f83])).
% 1.31/0.54  % (13096)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.31/0.54  fof(f83,plain,(
% 1.31/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.31/0.54    inference(equality_resolution,[],[f52])).
% 1.31/0.54  fof(f52,plain,(
% 1.31/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.31/0.54    inference(cnf_transformation,[],[f34])).
% 1.31/0.54  fof(f34,plain,(
% 1.31/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.31/0.54    inference(flattening,[],[f33])).
% 1.31/0.54  fof(f33,plain,(
% 1.31/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.31/0.54    inference(nnf_transformation,[],[f1])).
% 1.31/0.54  fof(f1,axiom,(
% 1.31/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.31/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.31/0.54  fof(f128,plain,(
% 1.31/0.54    ~r1_tarski(k3_xboole_0(k1_relat_1(sK2),sK1),k1_relat_1(sK2)) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2))),
% 1.31/0.54    inference(resolution,[],[f105,f115])).
% 1.31/0.54  fof(f115,plain,(
% 1.31/0.54    ~r1_tarski(k4_xboole_0(k1_relat_1(sK2),sK1),k1_relat_1(sK2))),
% 1.31/0.54    inference(subsumption_resolution,[],[f114,f41])).
% 1.31/0.54  fof(f41,plain,(
% 1.31/0.54    v1_relat_1(sK2)),
% 1.31/0.54    inference(cnf_transformation,[],[f32])).
% 1.31/0.54  fof(f32,plain,(
% 1.31/0.54    k6_subset_1(k1_relat_1(sK2),sK1) != k1_relat_1(k7_relat_1(sK2,k6_subset_1(k1_relat_1(sK2),sK1))) & v1_relat_1(sK2)),
% 1.31/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f22,f31])).
% 1.31/0.54  fof(f31,plain,(
% 1.31/0.54    ? [X0,X1] : (k6_subset_1(k1_relat_1(X1),X0) != k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))) & v1_relat_1(X1)) => (k6_subset_1(k1_relat_1(sK2),sK1) != k1_relat_1(k7_relat_1(sK2,k6_subset_1(k1_relat_1(sK2),sK1))) & v1_relat_1(sK2))),
% 1.31/0.54    introduced(choice_axiom,[])).
% 1.31/0.54  fof(f22,plain,(
% 1.31/0.54    ? [X0,X1] : (k6_subset_1(k1_relat_1(X1),X0) != k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))) & v1_relat_1(X1))),
% 1.31/0.54    inference(ennf_transformation,[],[f21])).
% 1.31/0.54  fof(f21,negated_conjecture,(
% 1.31/0.54    ~! [X0,X1] : (v1_relat_1(X1) => k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))))),
% 1.31/0.54    inference(negated_conjecture,[],[f20])).
% 1.31/0.54  fof(f20,conjecture,(
% 1.31/0.54    ! [X0,X1] : (v1_relat_1(X1) => k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,k6_subset_1(k1_relat_1(X1),X0))))),
% 1.31/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_relat_1)).
% 1.31/0.54  fof(f114,plain,(
% 1.31/0.54    ~r1_tarski(k4_xboole_0(k1_relat_1(sK2),sK1),k1_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 1.31/0.54    inference(trivial_inequality_removal,[],[f113])).
% 1.31/0.54  fof(f113,plain,(
% 1.31/0.54    k4_xboole_0(k1_relat_1(sK2),sK1) != k4_xboole_0(k1_relat_1(sK2),sK1) | ~r1_tarski(k4_xboole_0(k1_relat_1(sK2),sK1),k1_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 1.31/0.54    inference(superposition,[],[f94,f49])).
% 1.31/0.54  fof(f49,plain,(
% 1.31/0.54    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f24])).
% 1.31/0.54  fof(f24,plain,(
% 1.31/0.54    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.31/0.54    inference(flattening,[],[f23])).
% 1.31/0.54  fof(f23,plain,(
% 1.31/0.54    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.31/0.54    inference(ennf_transformation,[],[f19])).
% 1.31/0.54  fof(f19,axiom,(
% 1.31/0.54    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 1.31/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 1.31/0.54  fof(f94,plain,(
% 1.31/0.54    k4_xboole_0(k1_relat_1(sK2),sK1) != k1_relat_1(k7_relat_1(sK2,k4_xboole_0(k1_relat_1(sK2),sK1)))),
% 1.31/0.54    inference(forward_demodulation,[],[f42,f44])).
% 1.31/0.54  fof(f44,plain,(
% 1.31/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f16])).
% 1.31/0.54  fof(f16,axiom,(
% 1.31/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.31/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.31/0.54  fof(f42,plain,(
% 1.31/0.54    k6_subset_1(k1_relat_1(sK2),sK1) != k1_relat_1(k7_relat_1(sK2,k6_subset_1(k1_relat_1(sK2),sK1)))),
% 1.31/0.54    inference(cnf_transformation,[],[f32])).
% 1.31/0.54  fof(f105,plain,(
% 1.31/0.54    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(k3_xboole_0(X0,X1),X2) | ~r1_tarski(X0,X2)) )),
% 1.31/0.54    inference(superposition,[],[f55,f48])).
% 1.31/0.54  fof(f48,plain,(
% 1.31/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.31/0.54    inference(cnf_transformation,[],[f2])).
% 1.31/0.54  fof(f2,axiom,(
% 1.31/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.31/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.31/0.54  fof(f55,plain,(
% 1.31/0.54    ( ! [X2,X0,X1] : (r1_tarski(k5_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f27])).
% 1.31/0.54  fof(f27,plain,(
% 1.31/0.54    ! [X0,X1,X2] : (r1_tarski(k5_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 1.31/0.54    inference(flattening,[],[f26])).
% 1.31/0.54  fof(f26,plain,(
% 1.31/0.54    ! [X0,X1,X2] : (r1_tarski(k5_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 1.31/0.54    inference(ennf_transformation,[],[f3])).
% 1.31/0.54  fof(f3,axiom,(
% 1.31/0.54    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k5_xboole_0(X0,X2),X1))),
% 1.31/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_xboole_1)).
% 1.31/0.54  fof(f196,plain,(
% 1.31/0.54    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.31/0.54    inference(resolution,[],[f193,f96])).
% 1.31/0.54  fof(f96,plain,(
% 1.31/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,k2_tarski(X0,X1)) | r1_tarski(k3_xboole_0(X0,X1),X2)) )),
% 1.31/0.54    inference(superposition,[],[f50,f45])).
% 1.31/0.54  fof(f45,plain,(
% 1.31/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.31/0.54    inference(cnf_transformation,[],[f17])).
% 1.31/0.54  fof(f17,axiom,(
% 1.31/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.31/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.31/0.54  fof(f50,plain,(
% 1.31/0.54    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f25])).
% 1.31/0.54  fof(f25,plain,(
% 1.31/0.54    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1))),
% 1.31/0.54    inference(ennf_transformation,[],[f18])).
% 1.31/0.54  fof(f18,axiom,(
% 1.31/0.54    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 1.31/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).
% 1.31/0.54  fof(f193,plain,(
% 1.31/0.54    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X0,X1))) )),
% 1.31/0.54    inference(superposition,[],[f179,f47])).
% 1.31/0.54  fof(f47,plain,(
% 1.31/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f8])).
% 1.31/0.54  fof(f8,axiom,(
% 1.31/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.31/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.31/0.54  fof(f179,plain,(
% 1.31/0.54    ( ! [X12,X13,X11] : (r2_hidden(X13,k1_enumset1(X13,X12,X11))) )),
% 1.31/0.54    inference(superposition,[],[f175,f108])).
% 1.31/0.54  fof(f108,plain,(
% 1.31/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X2,X1,X0,X0)) )),
% 1.31/0.54    inference(superposition,[],[f56,f54])).
% 1.31/0.54  fof(f54,plain,(
% 1.31/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f9])).
% 1.31/0.54  fof(f9,axiom,(
% 1.31/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.31/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.31/0.54  fof(f56,plain,(
% 1.31/0.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f4])).
% 1.31/0.54  fof(f4,axiom,(
% 1.31/0.54    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)),
% 1.31/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).
% 1.31/0.54  fof(f175,plain,(
% 1.31/0.54    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,k2_enumset1(X0,X1,X2,X3))) )),
% 1.31/0.54    inference(superposition,[],[f169,f57])).
% 1.31/0.54  fof(f57,plain,(
% 1.31/0.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f10])).
% 1.31/0.54  fof(f10,axiom,(
% 1.31/0.54    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 1.31/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.31/0.54  fof(f169,plain,(
% 1.31/0.54    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(X4,k3_enumset1(X0,X1,X2,X3,X4))) )),
% 1.31/0.54    inference(superposition,[],[f164,f58])).
% 1.31/0.54  fof(f58,plain,(
% 1.31/0.54    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f11])).
% 1.31/0.54  fof(f11,axiom,(
% 1.31/0.54    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.31/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.31/0.54  fof(f164,plain,(
% 1.31/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (r2_hidden(X5,k4_enumset1(X0,X1,X2,X3,X4,X5))) )),
% 1.31/0.54    inference(superposition,[],[f161,f59])).
% 1.31/0.54  fof(f59,plain,(
% 1.31/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f12])).
% 1.31/0.54  fof(f12,axiom,(
% 1.31/0.54    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 1.31/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.31/0.54  fof(f161,plain,(
% 1.31/0.54    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r2_hidden(X6,k5_enumset1(X0,X1,X2,X3,X4,X5,X6))) )),
% 1.31/0.54    inference(superposition,[],[f152,f60])).
% 1.31/0.54  fof(f60,plain,(
% 1.31/0.54    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f13])).
% 1.31/0.54  fof(f13,axiom,(
% 1.31/0.54    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 1.31/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.31/0.54  fof(f152,plain,(
% 1.31/0.54    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r2_hidden(X0,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X0))) )),
% 1.31/0.54    inference(resolution,[],[f93,f85])).
% 1.31/0.54  fof(f85,plain,(
% 1.31/0.54    ( ! [X6,X4,X2,X10,X8,X7,X5,X3,X1] : (~sP0(X10,X1,X2,X3,X4,X5,X6,X7,X8) | r2_hidden(X10,X8)) )),
% 1.31/0.54    inference(equality_resolution,[],[f71])).
% 1.31/0.54  fof(f71,plain,(
% 1.31/0.54    ( ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] : (r2_hidden(X10,X8) | X0 != X10 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f39])).
% 1.31/0.54  fof(f39,plain,(
% 1.31/0.54    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) | (((sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X0 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X1 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X2 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X3 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X4 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X5 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X6 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X7) | ~r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)) & (sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X0 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X1 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X2 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X3 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X4 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X5 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X6 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X7 | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)))) & (! [X10] : ((r2_hidden(X10,X8) | (X0 != X10 & X1 != X10 & X2 != X10 & X3 != X10 & X4 != X10 & X5 != X10 & X6 != X10 & X7 != X10)) & (X0 = X10 | X1 = X10 | X2 = X10 | X3 = X10 | X4 = X10 | X5 = X10 | X6 = X10 | X7 = X10 | ~r2_hidden(X10,X8))) | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 1.31/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f37,f38])).
% 1.31/0.54  fof(f38,plain,(
% 1.31/0.54    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0] : (? [X9] : (((X0 != X9 & X1 != X9 & X2 != X9 & X3 != X9 & X4 != X9 & X5 != X9 & X6 != X9 & X7 != X9) | ~r2_hidden(X9,X8)) & (X0 = X9 | X1 = X9 | X2 = X9 | X3 = X9 | X4 = X9 | X5 = X9 | X6 = X9 | X7 = X9 | r2_hidden(X9,X8))) => (((sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X0 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X1 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X2 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X3 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X4 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X5 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X6 & sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X7) | ~r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)) & (sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X0 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X1 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X2 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X3 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X4 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X5 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X6 | sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X7 | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8))))),
% 1.31/0.54    introduced(choice_axiom,[])).
% 1.31/0.54  % (13117)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.31/0.54  % (13093)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.31/0.54  fof(f37,plain,(
% 1.31/0.54    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ? [X9] : (((X0 != X9 & X1 != X9 & X2 != X9 & X3 != X9 & X4 != X9 & X5 != X9 & X6 != X9 & X7 != X9) | ~r2_hidden(X9,X8)) & (X0 = X9 | X1 = X9 | X2 = X9 | X3 = X9 | X4 = X9 | X5 = X9 | X6 = X9 | X7 = X9 | r2_hidden(X9,X8)))) & (! [X10] : ((r2_hidden(X10,X8) | (X0 != X10 & X1 != X10 & X2 != X10 & X3 != X10 & X4 != X10 & X5 != X10 & X6 != X10 & X7 != X10)) & (X0 = X10 | X1 = X10 | X2 = X10 | X3 = X10 | X4 = X10 | X5 = X10 | X6 = X10 | X7 = X10 | ~r2_hidden(X10,X8))) | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 1.31/0.54    inference(rectify,[],[f36])).
% 1.31/0.54  % (13119)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.31/0.54  fof(f36,plain,(
% 1.31/0.54    ! [X7,X6,X5,X4,X3,X2,X1,X0,X8] : ((sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8) | ? [X9] : (((X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9) | ~r2_hidden(X9,X8)) & (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9 | r2_hidden(X9,X8)))) & (! [X9] : ((r2_hidden(X9,X8) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9 | ~r2_hidden(X9,X8))) | ~sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8)))),
% 1.31/0.54    inference(flattening,[],[f35])).
% 1.31/0.54  fof(f35,plain,(
% 1.31/0.54    ! [X7,X6,X5,X4,X3,X2,X1,X0,X8] : ((sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8) | ? [X9] : (((X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9) | ~r2_hidden(X9,X8)) & ((X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9) | r2_hidden(X9,X8)))) & (! [X9] : ((r2_hidden(X9,X8) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & ((X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9) | ~r2_hidden(X9,X8))) | ~sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8)))),
% 1.31/0.54    inference(nnf_transformation,[],[f29])).
% 1.31/0.54  fof(f29,plain,(
% 1.31/0.54    ! [X7,X6,X5,X4,X3,X2,X1,X0,X8] : (sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8) <=> ! [X9] : (r2_hidden(X9,X8) <=> (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9)))),
% 1.31/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.31/0.54  fof(f93,plain,(
% 1.31/0.54    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (sP0(X7,X6,X5,X4,X3,X2,X1,X0,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))) )),
% 1.31/0.54    inference(equality_resolution,[],[f81])).
% 1.31/0.54  fof(f81,plain,(
% 1.31/0.54    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8) )),
% 1.31/0.54    inference(cnf_transformation,[],[f40])).
% 1.31/0.54  fof(f40,plain,(
% 1.31/0.54    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 | ~sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8)) & (sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8))),
% 1.31/0.54    inference(nnf_transformation,[],[f30])).
% 1.31/0.54  fof(f30,plain,(
% 1.31/0.54    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8))),
% 1.31/0.54    inference(definition_folding,[],[f28,f29])).
% 1.31/0.54  fof(f28,plain,(
% 1.31/0.54    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9)))),
% 1.31/0.54    inference(ennf_transformation,[],[f15])).
% 1.31/0.54  fof(f15,axiom,(
% 1.31/0.54    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> ~(X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)))),
% 1.31/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_enumset1)).
% 1.31/0.54  % SZS output end Proof for theBenchmark
% 1.31/0.54  % (13101)------------------------------
% 1.31/0.54  % (13101)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.54  % (13101)Termination reason: Refutation
% 1.31/0.54  
% 1.31/0.54  % (13101)Memory used [KB]: 1791
% 1.31/0.54  % (13101)Time elapsed: 0.113 s
% 1.31/0.54  % (13101)------------------------------
% 1.31/0.54  % (13101)------------------------------
% 1.31/0.54  % (13100)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.31/0.54  % (13091)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.31/0.54  % (13087)Success in time 0.18 s
%------------------------------------------------------------------------------
