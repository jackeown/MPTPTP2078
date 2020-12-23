%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:15 EST 2020

% Result     : Theorem 1.61s
% Output     : Refutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 513 expanded)
%              Number of leaves         :   15 ( 133 expanded)
%              Depth                    :   34
%              Number of atoms          :  214 (1141 expanded)
%              Number of equality atoms :   28 ( 229 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f555,plain,(
    $false ),
    inference(subsumption_resolution,[],[f553,f37])).

fof(f37,plain,(
    ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
             => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

fof(f553,plain,(
    r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(resolution,[],[f547,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f547,plain,(
    r2_hidden(sK2(k3_relat_1(sK0),k3_relat_1(sK1)),k3_relat_1(sK1)) ),
    inference(resolution,[],[f545,f507])).

fof(f507,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))
    | r2_hidden(sK2(k3_relat_1(sK0),k3_relat_1(sK1)),k3_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f505,f197])).

fof(f197,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(sK0),X1)
      | r2_hidden(sK2(k3_relat_1(sK0),k3_relat_1(sK1)),X0)
      | r2_hidden(sK2(k3_relat_1(sK0),X0),X1)
      | ~ r1_tarski(k1_relat_1(sK0),X1) ) ),
    inference(resolution,[],[f156,f149])).

fof(f149,plain,(
    ! [X0] :
      ( r1_tarski(k3_relat_1(sK0),X0)
      | ~ r1_tarski(k2_relat_1(sK0),X0)
      | ~ r1_tarski(k1_relat_1(sK0),X0) ) ),
    inference(superposition,[],[f91,f116])).

fof(f116,plain,(
    k3_relat_1(sK0) = k3_tarski(k6_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k2_relat_1(sK0))) ),
    inference(resolution,[],[f38,f88])).

fof(f88,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k3_tarski(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(definition_unfolding,[],[f39,f87])).

fof(f87,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f44,f85])).

fof(f85,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f45,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f54,f83])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f59,f82])).

fof(f82,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f60,f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f61,f62])).

fof(f62,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f61,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f59,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f54,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f45,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(f38,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f58,f87])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X1)
      | r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f156,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k3_relat_1(sK0),X1)
      | r2_hidden(sK2(k3_relat_1(sK0),X0),X1)
      | r2_hidden(sK2(k3_relat_1(sK0),k3_relat_1(sK1)),X0) ) ),
    inference(resolution,[],[f136,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f136,plain,(
    ! [X1] :
      ( r2_hidden(sK2(k3_relat_1(sK0),X1),k3_relat_1(sK0))
      | r2_hidden(sK2(k3_relat_1(sK0),k3_relat_1(sK1)),X1) ) ),
    inference(resolution,[],[f118,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f118,plain,(
    ! [X0] :
      ( ~ r1_tarski(k3_relat_1(sK0),X0)
      | r2_hidden(sK2(k3_relat_1(sK0),k3_relat_1(sK1)),X0) ) ),
    inference(resolution,[],[f117,f47])).

fof(f117,plain,(
    r2_hidden(sK2(k3_relat_1(sK0),k3_relat_1(sK1)),k3_relat_1(sK0)) ),
    inference(resolution,[],[f37,f48])).

fof(f505,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))
    | r2_hidden(sK2(k3_relat_1(sK0),k3_relat_1(sK1)),k3_relat_1(sK1))
    | r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(resolution,[],[f498,f49])).

fof(f498,plain,(
    ! [X2] :
      ( r2_hidden(sK2(k2_relat_1(sK0),X2),k3_relat_1(sK1))
      | ~ r1_tarski(k1_relat_1(sK0),X2)
      | r2_hidden(sK2(k3_relat_1(sK0),k3_relat_1(sK1)),X2) ) ),
    inference(resolution,[],[f496,f122])).

fof(f122,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_relat_1(sK1))
      | r2_hidden(X1,k3_relat_1(sK1)) ) ),
    inference(resolution,[],[f112,f92])).

fof(f92,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(sK4(X0,X2),X2),X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X2),X2),X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f112,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),sK1)
      | r2_hidden(X3,k3_relat_1(sK1)) ) ),
    inference(resolution,[],[f35,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X1,k3_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).

fof(f35,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f496,plain,(
    ! [X0] :
      ( r2_hidden(sK2(k2_relat_1(sK0),X0),k2_relat_1(sK1))
      | r2_hidden(sK2(k3_relat_1(sK0),k3_relat_1(sK1)),X0)
      | ~ r1_tarski(k1_relat_1(sK0),X0) ) ),
    inference(subsumption_resolution,[],[f494,f36])).

fof(f36,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f494,plain,(
    ! [X0] :
      ( r2_hidden(sK2(k2_relat_1(sK0),X0),k2_relat_1(sK1))
      | r2_hidden(sK2(k3_relat_1(sK0),k3_relat_1(sK1)),X0)
      | ~ r1_tarski(k1_relat_1(sK0),X0)
      | ~ r1_tarski(sK0,sK1) ) ),
    inference(resolution,[],[f314,f35])).

fof(f314,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r2_hidden(sK2(k2_relat_1(sK0),X0),k2_relat_1(X1))
      | r2_hidden(sK2(k3_relat_1(sK0),k3_relat_1(sK1)),X0)
      | ~ r1_tarski(k1_relat_1(sK0),X0)
      | ~ r1_tarski(sK0,X1) ) ),
    inference(subsumption_resolution,[],[f311,f38])).

fof(f311,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(sK0),X0)
      | r2_hidden(sK2(k2_relat_1(sK0),X0),k2_relat_1(X1))
      | r2_hidden(sK2(k3_relat_1(sK0),k3_relat_1(sK1)),X0)
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(sK0,X1)
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f220,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(f220,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(k2_relat_1(sK0),X4)
      | ~ r1_tarski(k1_relat_1(sK0),X3)
      | r2_hidden(sK2(k2_relat_1(sK0),X3),X4)
      | r2_hidden(sK2(k3_relat_1(sK0),k3_relat_1(sK1)),X3) ) ),
    inference(resolution,[],[f181,f47])).

fof(f181,plain,(
    ! [X2] :
      ( r2_hidden(sK2(k2_relat_1(sK0),X2),k2_relat_1(sK0))
      | r2_hidden(sK2(k3_relat_1(sK0),k3_relat_1(sK1)),X2)
      | ~ r1_tarski(k1_relat_1(sK0),X2) ) ),
    inference(resolution,[],[f152,f48])).

fof(f152,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK0),X0)
      | ~ r1_tarski(k1_relat_1(sK0),X0)
      | r2_hidden(sK2(k3_relat_1(sK0),k3_relat_1(sK1)),X0) ) ),
    inference(resolution,[],[f149,f118])).

fof(f545,plain,(
    r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(resolution,[],[f541,f49])).

fof(f541,plain,(
    r2_hidden(sK2(k1_relat_1(sK0),k3_relat_1(sK1)),k3_relat_1(sK1)) ),
    inference(resolution,[],[f539,f133])).

fof(f133,plain,(
    r1_tarski(k1_relat_1(sK1),k3_relat_1(sK1)) ),
    inference(superposition,[],[f89,f113])).

fof(f113,plain,(
    k3_relat_1(sK1) = k3_tarski(k6_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k2_relat_1(sK1))) ),
    inference(resolution,[],[f35,f88])).

fof(f89,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f42,f87])).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f539,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK1),X0)
      | r2_hidden(sK2(k1_relat_1(sK0),k3_relat_1(sK1)),X0) ) ),
    inference(subsumption_resolution,[],[f537,f36])).

fof(f537,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK0,sK1)
      | r2_hidden(sK2(k1_relat_1(sK0),k3_relat_1(sK1)),X0)
      | ~ r1_tarski(k1_relat_1(sK1),X0) ) ),
    inference(resolution,[],[f525,f35])).

fof(f525,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r1_tarski(sK0,X0)
      | r2_hidden(sK2(k1_relat_1(sK0),k3_relat_1(sK1)),X1)
      | ~ r1_tarski(k1_relat_1(X0),X1) ) ),
    inference(resolution,[],[f520,f47])).

fof(f520,plain,(
    ! [X0] :
      ( r2_hidden(sK2(k1_relat_1(sK0),k3_relat_1(sK1)),k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f516,f38])).

fof(f516,plain,(
    ! [X0] :
      ( r2_hidden(sK2(k1_relat_1(sK0),k3_relat_1(sK1)),k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(sK0,X0)
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f515,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f515,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK0),X0)
      | r2_hidden(sK2(k1_relat_1(sK0),k3_relat_1(sK1)),X0) ) ),
    inference(subsumption_resolution,[],[f513,f37])).

fof(f513,plain,(
    ! [X0] :
      ( r2_hidden(sK2(k1_relat_1(sK0),k3_relat_1(sK1)),X0)
      | ~ r1_tarski(k1_relat_1(sK0),X0)
      | r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) ) ),
    inference(resolution,[],[f509,f49])).

fof(f509,plain,(
    ! [X0] :
      ( r2_hidden(sK2(k3_relat_1(sK0),k3_relat_1(sK1)),k3_relat_1(sK1))
      | r2_hidden(sK2(k1_relat_1(sK0),k3_relat_1(sK1)),X0)
      | ~ r1_tarski(k1_relat_1(sK0),X0) ) ),
    inference(resolution,[],[f508,f47])).

fof(f508,plain,
    ( r2_hidden(sK2(k1_relat_1(sK0),k3_relat_1(sK1)),k1_relat_1(sK0))
    | r2_hidden(sK2(k3_relat_1(sK0),k3_relat_1(sK1)),k3_relat_1(sK1)) ),
    inference(resolution,[],[f507,f48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:35:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (23413)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.53  % (23394)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.53  % (23394)Refutation not found, incomplete strategy% (23394)------------------------------
% 0.22/0.53  % (23394)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (23394)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (23394)Memory used [KB]: 10618
% 0.22/0.53  % (23394)Time elapsed: 0.107 s
% 0.22/0.53  % (23394)------------------------------
% 0.22/0.53  % (23394)------------------------------
% 0.22/0.53  % (23405)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.54  % (23387)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (23386)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (23384)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (23385)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (23388)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (23392)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.55  % (23414)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (23404)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % (23392)Refutation not found, incomplete strategy% (23392)------------------------------
% 0.22/0.55  % (23392)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (23392)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (23392)Memory used [KB]: 10874
% 0.22/0.55  % (23392)Time elapsed: 0.135 s
% 0.22/0.55  % (23392)------------------------------
% 0.22/0.55  % (23392)------------------------------
% 0.22/0.55  % (23399)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.55  % (23403)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.55  % (23397)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.41/0.55  % (23406)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.41/0.55  % (23409)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.41/0.55  % (23395)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.41/0.55  % (23396)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.41/0.55  % (23391)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.41/0.55  % (23383)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.41/0.56  % (23412)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.41/0.56  % (23411)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.41/0.56  % (23400)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.41/0.56  % (23408)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.41/0.56  % (23385)Refutation not found, incomplete strategy% (23385)------------------------------
% 1.41/0.56  % (23385)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.56  % (23385)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.56  
% 1.41/0.56  % (23385)Memory used [KB]: 10874
% 1.41/0.56  % (23385)Time elapsed: 0.134 s
% 1.41/0.56  % (23385)------------------------------
% 1.41/0.56  % (23385)------------------------------
% 1.41/0.56  % (23395)Refutation not found, incomplete strategy% (23395)------------------------------
% 1.41/0.56  % (23395)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.56  % (23402)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.61/0.57  % (23383)Refutation not found, incomplete strategy% (23383)------------------------------
% 1.61/0.57  % (23383)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.57  % (23407)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.61/0.57  % (23395)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.57  
% 1.61/0.57  % (23395)Memory used [KB]: 10618
% 1.61/0.57  % (23395)Time elapsed: 0.147 s
% 1.61/0.57  % (23395)------------------------------
% 1.61/0.57  % (23395)------------------------------
% 1.61/0.57  % (23410)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.61/0.57  % (23383)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.57  
% 1.61/0.57  % (23383)Memory used [KB]: 1663
% 1.61/0.57  % (23383)Time elapsed: 0.152 s
% 1.61/0.57  % (23383)------------------------------
% 1.61/0.57  % (23383)------------------------------
% 1.61/0.58  % (23398)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.61/0.58  % (23402)Refutation not found, incomplete strategy% (23402)------------------------------
% 1.61/0.58  % (23402)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.58  % (23402)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.58  
% 1.61/0.58  % (23402)Memory used [KB]: 10618
% 1.61/0.58  % (23402)Time elapsed: 0.165 s
% 1.61/0.58  % (23402)------------------------------
% 1.61/0.58  % (23402)------------------------------
% 1.61/0.58  % (23393)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.61/0.58  % (23393)Refutation not found, incomplete strategy% (23393)------------------------------
% 1.61/0.58  % (23393)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.58  % (23393)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.58  
% 1.61/0.58  % (23393)Memory used [KB]: 10618
% 1.61/0.58  % (23393)Time elapsed: 0.167 s
% 1.61/0.58  % (23393)------------------------------
% 1.61/0.58  % (23393)------------------------------
% 1.61/0.58  % (23407)Refutation not found, incomplete strategy% (23407)------------------------------
% 1.61/0.58  % (23407)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.58  % (23390)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.61/0.59  % (23407)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.59  
% 1.61/0.59  % (23407)Memory used [KB]: 10746
% 1.61/0.59  % (23407)Time elapsed: 0.092 s
% 1.61/0.59  % (23407)------------------------------
% 1.61/0.59  % (23407)------------------------------
% 1.61/0.61  % (23406)Refutation found. Thanks to Tanya!
% 1.61/0.61  % SZS status Theorem for theBenchmark
% 1.61/0.61  % SZS output start Proof for theBenchmark
% 1.61/0.61  fof(f555,plain,(
% 1.61/0.61    $false),
% 1.61/0.61    inference(subsumption_resolution,[],[f553,f37])).
% 1.61/0.61  fof(f37,plain,(
% 1.61/0.61    ~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))),
% 1.61/0.61    inference(cnf_transformation,[],[f22])).
% 1.61/0.61  fof(f22,plain,(
% 1.61/0.61    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.61/0.61    inference(flattening,[],[f21])).
% 1.61/0.61  fof(f21,plain,(
% 1.61/0.61    ? [X0] : (? [X1] : ((~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.61/0.61    inference(ennf_transformation,[],[f20])).
% 1.61/0.61  fof(f20,negated_conjecture,(
% 1.61/0.61    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 1.61/0.61    inference(negated_conjecture,[],[f19])).
% 1.61/0.61  fof(f19,conjecture,(
% 1.61/0.61    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 1.61/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).
% 1.61/0.61  fof(f553,plain,(
% 1.61/0.61    r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))),
% 1.61/0.61    inference(resolution,[],[f547,f49])).
% 1.61/0.61  fof(f49,plain,(
% 1.61/0.61    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.61/0.61    inference(cnf_transformation,[],[f27])).
% 1.61/0.61  fof(f27,plain,(
% 1.61/0.61    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.61/0.61    inference(ennf_transformation,[],[f1])).
% 1.61/0.61  fof(f1,axiom,(
% 1.61/0.61    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.61/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.61/0.61  fof(f547,plain,(
% 1.61/0.61    r2_hidden(sK2(k3_relat_1(sK0),k3_relat_1(sK1)),k3_relat_1(sK1))),
% 1.61/0.61    inference(resolution,[],[f545,f507])).
% 1.61/0.61  fof(f507,plain,(
% 1.61/0.61    ~r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) | r2_hidden(sK2(k3_relat_1(sK0),k3_relat_1(sK1)),k3_relat_1(sK1))),
% 1.61/0.61    inference(subsumption_resolution,[],[f505,f197])).
% 1.61/0.61  fof(f197,plain,(
% 1.61/0.61    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(sK0),X1) | r2_hidden(sK2(k3_relat_1(sK0),k3_relat_1(sK1)),X0) | r2_hidden(sK2(k3_relat_1(sK0),X0),X1) | ~r1_tarski(k1_relat_1(sK0),X1)) )),
% 1.61/0.61    inference(resolution,[],[f156,f149])).
% 1.61/0.61  fof(f149,plain,(
% 1.61/0.61    ( ! [X0] : (r1_tarski(k3_relat_1(sK0),X0) | ~r1_tarski(k2_relat_1(sK0),X0) | ~r1_tarski(k1_relat_1(sK0),X0)) )),
% 1.61/0.61    inference(superposition,[],[f91,f116])).
% 1.61/0.61  fof(f116,plain,(
% 1.61/0.61    k3_relat_1(sK0) = k3_tarski(k6_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k2_relat_1(sK0)))),
% 1.61/0.61    inference(resolution,[],[f38,f88])).
% 1.61/0.61  fof(f88,plain,(
% 1.61/0.61    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k3_tarski(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0)))) )),
% 1.61/0.61    inference(definition_unfolding,[],[f39,f87])).
% 1.61/0.61  fof(f87,plain,(
% 1.61/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.61/0.61    inference(definition_unfolding,[],[f44,f85])).
% 1.61/0.61  fof(f85,plain,(
% 1.61/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.61/0.61    inference(definition_unfolding,[],[f45,f84])).
% 1.61/0.61  fof(f84,plain,(
% 1.61/0.61    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.61/0.61    inference(definition_unfolding,[],[f54,f83])).
% 1.61/0.61  fof(f83,plain,(
% 1.61/0.61    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.61/0.61    inference(definition_unfolding,[],[f59,f82])).
% 1.61/0.61  fof(f82,plain,(
% 1.61/0.61    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.61/0.61    inference(definition_unfolding,[],[f60,f81])).
% 1.61/0.61  fof(f81,plain,(
% 1.61/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.61/0.61    inference(definition_unfolding,[],[f61,f62])).
% 1.61/0.61  fof(f62,plain,(
% 1.61/0.61    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.61/0.61    inference(cnf_transformation,[],[f10])).
% 1.61/0.61  fof(f10,axiom,(
% 1.61/0.61    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.61/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.61/0.61  fof(f61,plain,(
% 1.61/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.61/0.61    inference(cnf_transformation,[],[f9])).
% 1.61/0.61  fof(f9,axiom,(
% 1.61/0.61    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.61/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.61/0.61  fof(f60,plain,(
% 1.61/0.61    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.61/0.61    inference(cnf_transformation,[],[f8])).
% 1.61/0.61  fof(f8,axiom,(
% 1.61/0.61    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.61/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.61/0.61  fof(f59,plain,(
% 1.61/0.61    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.61/0.61    inference(cnf_transformation,[],[f7])).
% 1.61/0.61  fof(f7,axiom,(
% 1.61/0.61    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.61/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.61/0.61  fof(f54,plain,(
% 1.61/0.61    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.61/0.61    inference(cnf_transformation,[],[f6])).
% 1.61/0.61  fof(f6,axiom,(
% 1.61/0.61    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.61/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.61/0.61  fof(f45,plain,(
% 1.61/0.61    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.61/0.61    inference(cnf_transformation,[],[f5])).
% 1.61/0.61  fof(f5,axiom,(
% 1.61/0.61    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.61/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.61/0.61  fof(f44,plain,(
% 1.61/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.61/0.61    inference(cnf_transformation,[],[f11])).
% 1.61/0.61  fof(f11,axiom,(
% 1.61/0.61    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.61/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.61/0.61  fof(f39,plain,(
% 1.61/0.61    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))) )),
% 1.61/0.61    inference(cnf_transformation,[],[f23])).
% 1.61/0.61  fof(f23,plain,(
% 1.61/0.61    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.61/0.61    inference(ennf_transformation,[],[f16])).
% 1.61/0.61  fof(f16,axiom,(
% 1.61/0.61    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 1.61/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).
% 1.61/0.61  fof(f38,plain,(
% 1.61/0.61    v1_relat_1(sK0)),
% 1.61/0.61    inference(cnf_transformation,[],[f22])).
% 1.61/0.61  fof(f91,plain,(
% 1.61/0.61    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.61/0.61    inference(definition_unfolding,[],[f58,f87])).
% 1.61/0.61  fof(f58,plain,(
% 1.61/0.61    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X2,X1) | r1_tarski(k2_xboole_0(X0,X2),X1)) )),
% 1.61/0.61    inference(cnf_transformation,[],[f33])).
% 1.61/0.61  fof(f33,plain,(
% 1.61/0.61    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 1.61/0.61    inference(flattening,[],[f32])).
% 1.61/0.61  fof(f32,plain,(
% 1.61/0.61    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 1.61/0.61    inference(ennf_transformation,[],[f4])).
% 1.61/0.61  fof(f4,axiom,(
% 1.61/0.61    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 1.61/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).
% 1.61/0.61  fof(f156,plain,(
% 1.61/0.61    ( ! [X0,X1] : (~r1_tarski(k3_relat_1(sK0),X1) | r2_hidden(sK2(k3_relat_1(sK0),X0),X1) | r2_hidden(sK2(k3_relat_1(sK0),k3_relat_1(sK1)),X0)) )),
% 1.61/0.61    inference(resolution,[],[f136,f47])).
% 1.61/0.61  fof(f47,plain,(
% 1.61/0.61    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.61/0.61    inference(cnf_transformation,[],[f27])).
% 1.61/0.61  fof(f136,plain,(
% 1.61/0.61    ( ! [X1] : (r2_hidden(sK2(k3_relat_1(sK0),X1),k3_relat_1(sK0)) | r2_hidden(sK2(k3_relat_1(sK0),k3_relat_1(sK1)),X1)) )),
% 1.61/0.61    inference(resolution,[],[f118,f48])).
% 1.61/0.61  fof(f48,plain,(
% 1.61/0.61    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 1.61/0.61    inference(cnf_transformation,[],[f27])).
% 1.61/0.61  fof(f118,plain,(
% 1.61/0.61    ( ! [X0] : (~r1_tarski(k3_relat_1(sK0),X0) | r2_hidden(sK2(k3_relat_1(sK0),k3_relat_1(sK1)),X0)) )),
% 1.61/0.61    inference(resolution,[],[f117,f47])).
% 1.61/0.61  fof(f117,plain,(
% 1.61/0.61    r2_hidden(sK2(k3_relat_1(sK0),k3_relat_1(sK1)),k3_relat_1(sK0))),
% 1.61/0.61    inference(resolution,[],[f37,f48])).
% 1.61/0.61  fof(f505,plain,(
% 1.61/0.61    ~r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) | r2_hidden(sK2(k3_relat_1(sK0),k3_relat_1(sK1)),k3_relat_1(sK1)) | r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1))),
% 1.61/0.61    inference(resolution,[],[f498,f49])).
% 1.61/0.61  fof(f498,plain,(
% 1.61/0.61    ( ! [X2] : (r2_hidden(sK2(k2_relat_1(sK0),X2),k3_relat_1(sK1)) | ~r1_tarski(k1_relat_1(sK0),X2) | r2_hidden(sK2(k3_relat_1(sK0),k3_relat_1(sK1)),X2)) )),
% 1.61/0.61    inference(resolution,[],[f496,f122])).
% 1.61/0.61  fof(f122,plain,(
% 1.61/0.61    ( ! [X1] : (~r2_hidden(X1,k2_relat_1(sK1)) | r2_hidden(X1,k3_relat_1(sK1))) )),
% 1.61/0.61    inference(resolution,[],[f112,f92])).
% 1.61/0.61  fof(f92,plain,(
% 1.61/0.61    ( ! [X2,X0] : (r2_hidden(k4_tarski(sK4(X0,X2),X2),X0) | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 1.61/0.61    inference(equality_resolution,[],[f51])).
% 1.61/0.61  fof(f51,plain,(
% 1.61/0.61    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK4(X0,X2),X2),X0) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 1.61/0.61    inference(cnf_transformation,[],[f15])).
% 1.61/0.61  fof(f15,axiom,(
% 1.61/0.61    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 1.61/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 1.61/0.61  fof(f112,plain,(
% 1.61/0.61    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),sK1) | r2_hidden(X3,k3_relat_1(sK1))) )),
% 1.61/0.61    inference(resolution,[],[f35,f56])).
% 1.61/0.61  fof(f56,plain,(
% 1.61/0.61    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X1,k3_relat_1(X2))) )),
% 1.61/0.61    inference(cnf_transformation,[],[f29])).
% 1.61/0.61  fof(f29,plain,(
% 1.61/0.61    ! [X0,X1,X2] : ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 1.61/0.61    inference(flattening,[],[f28])).
% 1.61/0.61  fof(f28,plain,(
% 1.61/0.61    ! [X0,X1,X2] : (((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 1.61/0.61    inference(ennf_transformation,[],[f18])).
% 1.61/0.61  fof(f18,axiom,(
% 1.61/0.61    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)))))),
% 1.61/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).
% 1.61/0.61  fof(f35,plain,(
% 1.61/0.61    v1_relat_1(sK1)),
% 1.61/0.61    inference(cnf_transformation,[],[f22])).
% 1.61/0.61  fof(f496,plain,(
% 1.61/0.61    ( ! [X0] : (r2_hidden(sK2(k2_relat_1(sK0),X0),k2_relat_1(sK1)) | r2_hidden(sK2(k3_relat_1(sK0),k3_relat_1(sK1)),X0) | ~r1_tarski(k1_relat_1(sK0),X0)) )),
% 1.61/0.61    inference(subsumption_resolution,[],[f494,f36])).
% 1.61/0.61  fof(f36,plain,(
% 1.61/0.61    r1_tarski(sK0,sK1)),
% 1.61/0.61    inference(cnf_transformation,[],[f22])).
% 1.61/0.61  fof(f494,plain,(
% 1.61/0.61    ( ! [X0] : (r2_hidden(sK2(k2_relat_1(sK0),X0),k2_relat_1(sK1)) | r2_hidden(sK2(k3_relat_1(sK0),k3_relat_1(sK1)),X0) | ~r1_tarski(k1_relat_1(sK0),X0) | ~r1_tarski(sK0,sK1)) )),
% 1.61/0.61    inference(resolution,[],[f314,f35])).
% 1.61/0.61  fof(f314,plain,(
% 1.61/0.61    ( ! [X0,X1] : (~v1_relat_1(X1) | r2_hidden(sK2(k2_relat_1(sK0),X0),k2_relat_1(X1)) | r2_hidden(sK2(k3_relat_1(sK0),k3_relat_1(sK1)),X0) | ~r1_tarski(k1_relat_1(sK0),X0) | ~r1_tarski(sK0,X1)) )),
% 1.61/0.61    inference(subsumption_resolution,[],[f311,f38])).
% 1.61/0.61  fof(f311,plain,(
% 1.61/0.61    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(sK0),X0) | r2_hidden(sK2(k2_relat_1(sK0),X0),k2_relat_1(X1)) | r2_hidden(sK2(k3_relat_1(sK0),k3_relat_1(sK1)),X0) | ~v1_relat_1(X1) | ~r1_tarski(sK0,X1) | ~v1_relat_1(sK0)) )),
% 1.61/0.61    inference(resolution,[],[f220,f41])).
% 1.61/0.61  fof(f41,plain,(
% 1.61/0.61    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 1.61/0.61    inference(cnf_transformation,[],[f25])).
% 1.61/0.61  fof(f25,plain,(
% 1.61/0.61    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.61/0.61    inference(flattening,[],[f24])).
% 1.61/0.61  fof(f24,plain,(
% 1.61/0.61    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.61/0.61    inference(ennf_transformation,[],[f17])).
% 1.61/0.61  fof(f17,axiom,(
% 1.61/0.61    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 1.61/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).
% 1.61/0.61  fof(f220,plain,(
% 1.61/0.61    ( ! [X4,X3] : (~r1_tarski(k2_relat_1(sK0),X4) | ~r1_tarski(k1_relat_1(sK0),X3) | r2_hidden(sK2(k2_relat_1(sK0),X3),X4) | r2_hidden(sK2(k3_relat_1(sK0),k3_relat_1(sK1)),X3)) )),
% 1.61/0.61    inference(resolution,[],[f181,f47])).
% 1.61/0.61  fof(f181,plain,(
% 1.61/0.61    ( ! [X2] : (r2_hidden(sK2(k2_relat_1(sK0),X2),k2_relat_1(sK0)) | r2_hidden(sK2(k3_relat_1(sK0),k3_relat_1(sK1)),X2) | ~r1_tarski(k1_relat_1(sK0),X2)) )),
% 1.61/0.61    inference(resolution,[],[f152,f48])).
% 1.61/0.61  fof(f152,plain,(
% 1.61/0.61    ( ! [X0] : (~r1_tarski(k2_relat_1(sK0),X0) | ~r1_tarski(k1_relat_1(sK0),X0) | r2_hidden(sK2(k3_relat_1(sK0),k3_relat_1(sK1)),X0)) )),
% 1.61/0.61    inference(resolution,[],[f149,f118])).
% 1.61/0.61  fof(f545,plain,(
% 1.61/0.61    r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))),
% 1.61/0.61    inference(resolution,[],[f541,f49])).
% 1.61/0.61  fof(f541,plain,(
% 1.61/0.61    r2_hidden(sK2(k1_relat_1(sK0),k3_relat_1(sK1)),k3_relat_1(sK1))),
% 1.61/0.61    inference(resolution,[],[f539,f133])).
% 1.61/0.61  fof(f133,plain,(
% 1.61/0.61    r1_tarski(k1_relat_1(sK1),k3_relat_1(sK1))),
% 1.61/0.61    inference(superposition,[],[f89,f113])).
% 1.61/0.61  fof(f113,plain,(
% 1.61/0.61    k3_relat_1(sK1) = k3_tarski(k6_enumset1(k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k1_relat_1(sK1),k2_relat_1(sK1)))),
% 1.61/0.61    inference(resolution,[],[f35,f88])).
% 1.61/0.61  fof(f89,plain,(
% 1.61/0.61    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.61/0.61    inference(definition_unfolding,[],[f42,f87])).
% 1.61/0.61  fof(f42,plain,(
% 1.61/0.61    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.61/0.61    inference(cnf_transformation,[],[f3])).
% 1.61/0.61  fof(f3,axiom,(
% 1.61/0.61    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.61/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.61/0.61  fof(f539,plain,(
% 1.61/0.61    ( ! [X0] : (~r1_tarski(k1_relat_1(sK1),X0) | r2_hidden(sK2(k1_relat_1(sK0),k3_relat_1(sK1)),X0)) )),
% 1.61/0.61    inference(subsumption_resolution,[],[f537,f36])).
% 1.61/0.61  fof(f537,plain,(
% 1.61/0.61    ( ! [X0] : (~r1_tarski(sK0,sK1) | r2_hidden(sK2(k1_relat_1(sK0),k3_relat_1(sK1)),X0) | ~r1_tarski(k1_relat_1(sK1),X0)) )),
% 1.61/0.61    inference(resolution,[],[f525,f35])).
% 1.61/0.61  fof(f525,plain,(
% 1.61/0.61    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r1_tarski(sK0,X0) | r2_hidden(sK2(k1_relat_1(sK0),k3_relat_1(sK1)),X1) | ~r1_tarski(k1_relat_1(X0),X1)) )),
% 1.61/0.61    inference(resolution,[],[f520,f47])).
% 1.61/0.61  fof(f520,plain,(
% 1.61/0.61    ( ! [X0] : (r2_hidden(sK2(k1_relat_1(sK0),k3_relat_1(sK1)),k1_relat_1(X0)) | ~v1_relat_1(X0) | ~r1_tarski(sK0,X0)) )),
% 1.61/0.61    inference(subsumption_resolution,[],[f516,f38])).
% 1.61/0.61  fof(f516,plain,(
% 1.61/0.61    ( ! [X0] : (r2_hidden(sK2(k1_relat_1(sK0),k3_relat_1(sK1)),k1_relat_1(X0)) | ~v1_relat_1(X0) | ~r1_tarski(sK0,X0) | ~v1_relat_1(sK0)) )),
% 1.61/0.61    inference(resolution,[],[f515,f40])).
% 1.61/0.61  fof(f40,plain,(
% 1.61/0.61    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 1.61/0.61    inference(cnf_transformation,[],[f25])).
% 1.61/0.61  fof(f515,plain,(
% 1.61/0.61    ( ! [X0] : (~r1_tarski(k1_relat_1(sK0),X0) | r2_hidden(sK2(k1_relat_1(sK0),k3_relat_1(sK1)),X0)) )),
% 1.61/0.61    inference(subsumption_resolution,[],[f513,f37])).
% 1.61/0.61  fof(f513,plain,(
% 1.61/0.61    ( ! [X0] : (r2_hidden(sK2(k1_relat_1(sK0),k3_relat_1(sK1)),X0) | ~r1_tarski(k1_relat_1(sK0),X0) | r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))) )),
% 1.61/0.61    inference(resolution,[],[f509,f49])).
% 1.61/0.61  fof(f509,plain,(
% 1.61/0.61    ( ! [X0] : (r2_hidden(sK2(k3_relat_1(sK0),k3_relat_1(sK1)),k3_relat_1(sK1)) | r2_hidden(sK2(k1_relat_1(sK0),k3_relat_1(sK1)),X0) | ~r1_tarski(k1_relat_1(sK0),X0)) )),
% 1.61/0.61    inference(resolution,[],[f508,f47])).
% 1.61/0.61  fof(f508,plain,(
% 1.61/0.61    r2_hidden(sK2(k1_relat_1(sK0),k3_relat_1(sK1)),k1_relat_1(sK0)) | r2_hidden(sK2(k3_relat_1(sK0),k3_relat_1(sK1)),k3_relat_1(sK1))),
% 1.61/0.61    inference(resolution,[],[f507,f48])).
% 1.61/0.61  % SZS output end Proof for theBenchmark
% 1.61/0.61  % (23406)------------------------------
% 1.61/0.61  % (23406)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.61  % (23406)Termination reason: Refutation
% 1.61/0.61  
% 1.61/0.61  % (23406)Memory used [KB]: 2174
% 1.61/0.61  % (23406)Time elapsed: 0.190 s
% 1.61/0.61  % (23406)------------------------------
% 1.61/0.61  % (23406)------------------------------
% 1.61/0.61  % (23382)Success in time 0.247 s
%------------------------------------------------------------------------------
