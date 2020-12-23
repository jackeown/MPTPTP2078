%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:29 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 267 expanded)
%              Number of leaves         :   15 (  59 expanded)
%              Depth                    :   15
%              Number of atoms          :  206 ( 722 expanded)
%              Number of equality atoms :   43 (  82 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1149,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1119,f71])).

fof(f71,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f63,f49])).

fof(f49,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f1119,plain,(
    ~ r1_xboole_0(k1_xboole_0,k9_relat_1(sK2,sK1)) ),
    inference(backward_demodulation,[],[f430,f1098])).

fof(f1098,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f1089,f1079])).

fof(f1079,plain,(
    ! [X0] : ~ r2_hidden(X0,k2_relat_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f1070,f75])).

fof(f75,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f66,f49])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(f1070,plain,(
    ! [X0] :
      ( r2_hidden(sK10(k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(X0,k2_relat_1(k1_xboole_0)) ) ),
    inference(backward_demodulation,[],[f242,f1068])).

fof(f1068,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f1065,f73])).

fof(f73,plain,(
    k1_xboole_0 = k7_relat_1(sK2,k1_xboole_0) ),
    inference(resolution,[],[f52,f43])).

fof(f43,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v2_funct_1(X2)
      & r1_xboole_0(X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v2_funct_1(X2)
      & r1_xboole_0(X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( v2_funct_1(X2)
            & r1_xboole_0(X0,X1) )
         => r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_xboole_0(X0,X1) )
       => r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_funct_1)).

fof(f52,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_relat_1)).

fof(f1065,plain,(
    k1_xboole_0 = k1_relat_1(k7_relat_1(sK2,k1_xboole_0)) ),
    inference(resolution,[],[f155,f43])).

fof(f155,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k1_relat_1(k7_relat_1(X0,k1_xboole_0)) ) ),
    inference(resolution,[],[f125,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f125,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(subsumption_resolution,[],[f119,f75])).

fof(f119,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK5(k1_xboole_0,X0),sK6(k1_xboole_0,X0)),k1_xboole_0)
      | r1_tarski(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f97,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

fof(f97,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f75,f58])).

fof(f58,plain,(
    ! [X0] :
      ( r2_hidden(sK7(X0),X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(f242,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(k1_xboole_0))
      | r2_hidden(sK10(k1_xboole_0),k1_relat_1(k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f241,f73])).

fof(f241,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(k1_xboole_0))
      | r2_hidden(sK10(k7_relat_1(sK2,k1_xboole_0)),k1_relat_1(k7_relat_1(sK2,k1_xboole_0))) ) ),
    inference(subsumption_resolution,[],[f240,f97])).

fof(f240,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k1_xboole_0)
      | ~ r2_hidden(X0,k2_relat_1(k1_xboole_0))
      | r2_hidden(sK10(k7_relat_1(sK2,k1_xboole_0)),k1_relat_1(k7_relat_1(sK2,k1_xboole_0))) ) ),
    inference(forward_demodulation,[],[f239,f73])).

fof(f239,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k7_relat_1(sK2,k1_xboole_0))
      | r2_hidden(sK10(k7_relat_1(sK2,k1_xboole_0)),k1_relat_1(k7_relat_1(sK2,k1_xboole_0))) ) ),
    inference(superposition,[],[f99,f98])).

fof(f98,plain,(
    k9_relat_1(sK2,k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f77,f73])).

fof(f77,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    inference(resolution,[],[f60,f43])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k9_relat_1(sK2,X0))
      | ~ v1_relat_1(k7_relat_1(sK2,X0))
      | r2_hidden(sK10(k7_relat_1(sK2,X0)),k1_relat_1(k7_relat_1(sK2,X0))) ) ),
    inference(superposition,[],[f62,f77])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | r2_hidden(sK10(X1),k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( ! [X2] : ~ r2_hidden(X2,k1_relat_1(X1))
          & r2_hidden(X0,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relat_1)).

fof(f1089,plain,
    ( r2_hidden(k4_tarski(sK3(k2_relat_1(k1_xboole_0)),sK4(k2_relat_1(k1_xboole_0))),k2_relat_1(k1_xboole_0))
    | k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f1078,f53])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).

fof(f1078,plain,(
    v1_relat_1(k2_relat_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f1069,f75])).

fof(f1069,plain,
    ( r2_hidden(sK10(k1_xboole_0),k1_xboole_0)
    | v1_relat_1(k2_relat_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f135,f1068])).

fof(f135,plain,
    ( r2_hidden(sK10(k1_xboole_0),k1_relat_1(k1_xboole_0))
    | v1_relat_1(k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f81,f97])).

fof(f81,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK10(X0),k1_relat_1(X0))
      | v1_relat_1(k2_relat_1(X0)) ) ),
    inference(resolution,[],[f62,f58])).

fof(f430,plain,(
    ~ r1_xboole_0(k2_relat_1(k1_xboole_0),k9_relat_1(sK2,sK1)) ),
    inference(subsumption_resolution,[],[f425,f47])).

fof(f47,plain,(
    ~ r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f425,plain,
    ( ~ r1_xboole_0(k2_relat_1(k1_xboole_0),k9_relat_1(sK2,sK1))
    | r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(superposition,[],[f136,f179])).

fof(f179,plain,(
    k2_relat_1(k1_xboole_0) = k9_relat_1(sK2,k3_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f77,f108])).

fof(f108,plain,(
    k1_xboole_0 = k7_relat_1(sK2,k3_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f90,f45])).

fof(f45,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k7_relat_1(sK2,k3_xboole_0(X0,X1)) ) ),
    inference(backward_demodulation,[],[f86,f88])).

fof(f88,plain,(
    ! [X0,X1] : k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k3_xboole_0(X0,X1)) ),
    inference(resolution,[],[f67,f43])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,X0),X1) ) ),
    inference(resolution,[],[f68,f43])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_xboole_0(X0,X1)
       => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).

fof(f136,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k9_relat_1(sK2,k3_xboole_0(X0,X1)),k9_relat_1(sK2,X1))
      | r1_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) ) ),
    inference(superposition,[],[f65,f96])).

fof(f96,plain,(
    ! [X0,X1] : k9_relat_1(sK2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) ),
    inference(subsumption_resolution,[],[f95,f43])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK2)
      | k9_relat_1(sK2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) ) ),
    inference(subsumption_resolution,[],[f94,f44])).

fof(f44,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2)
      | k9_relat_1(sK2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) ) ),
    inference(resolution,[],[f69,f46])).

fof(f46,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_1)).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( r1_xboole_0(k3_xboole_0(X0,X1),X1)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n020.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 14:24:37 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.48  % (15754)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (15761)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.50  % (15757)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.50  % (15765)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.51  % (15748)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (15753)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (15756)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.52  % (15751)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (15763)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.53  % (15750)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.53  % (15749)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (15755)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.53  % (15760)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (15749)Refutation not found, incomplete strategy% (15749)------------------------------
% 0.21/0.53  % (15749)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (15749)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (15749)Memory used [KB]: 10618
% 0.21/0.53  % (15749)Time elapsed: 0.104 s
% 0.21/0.53  % (15749)------------------------------
% 0.21/0.53  % (15749)------------------------------
% 0.21/0.53  % (15764)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.54  % (15762)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.54  % (15768)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.54  % (15758)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.54  % (15768)Refutation not found, incomplete strategy% (15768)------------------------------
% 0.21/0.54  % (15768)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (15768)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (15768)Memory used [KB]: 10618
% 0.21/0.54  % (15768)Time elapsed: 0.116 s
% 0.21/0.54  % (15768)------------------------------
% 0.21/0.54  % (15768)------------------------------
% 0.21/0.54  % (15752)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.55  % (15766)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.55  % (15767)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.55  % (15759)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.56  % (15765)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.56  % SZS output start Proof for theBenchmark
% 0.21/0.56  fof(f1149,plain,(
% 0.21/0.56    $false),
% 0.21/0.56    inference(subsumption_resolution,[],[f1119,f71])).
% 0.21/0.56  fof(f71,plain,(
% 0.21/0.56    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.56    inference(resolution,[],[f63,f49])).
% 0.21/0.56  fof(f49,plain,(
% 0.21/0.56    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f2])).
% 0.21/0.56  fof(f2,axiom,(
% 0.21/0.56    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.56  fof(f63,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f33])).
% 0.21/0.56  fof(f33,plain,(
% 0.21/0.56    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.56    inference(ennf_transformation,[],[f1])).
% 0.21/0.56  fof(f1,axiom,(
% 0.21/0.56    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.21/0.56  fof(f1119,plain,(
% 0.21/0.56    ~r1_xboole_0(k1_xboole_0,k9_relat_1(sK2,sK1))),
% 0.21/0.56    inference(backward_demodulation,[],[f430,f1098])).
% 0.21/0.56  fof(f1098,plain,(
% 0.21/0.56    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.56    inference(subsumption_resolution,[],[f1089,f1079])).
% 0.21/0.56  fof(f1079,plain,(
% 0.21/0.56    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(k1_xboole_0))) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f1070,f75])).
% 0.21/0.56  fof(f75,plain,(
% 0.21/0.56    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.56    inference(resolution,[],[f66,f49])).
% 0.21/0.56  fof(f66,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r1_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f37])).
% 0.21/0.56  fof(f37,plain,(
% 0.21/0.56    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.56    inference(ennf_transformation,[],[f4])).
% 0.21/0.56  fof(f4,axiom,(
% 0.21/0.56    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).
% 0.21/0.56  fof(f1070,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(sK10(k1_xboole_0),k1_xboole_0) | ~r2_hidden(X0,k2_relat_1(k1_xboole_0))) )),
% 0.21/0.56    inference(backward_demodulation,[],[f242,f1068])).
% 0.21/0.56  fof(f1068,plain,(
% 0.21/0.56    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.56    inference(forward_demodulation,[],[f1065,f73])).
% 0.21/0.56  fof(f73,plain,(
% 0.21/0.56    k1_xboole_0 = k7_relat_1(sK2,k1_xboole_0)),
% 0.21/0.56    inference(resolution,[],[f52,f43])).
% 0.21/0.56  fof(f43,plain,(
% 0.21/0.56    v1_relat_1(sK2)),
% 0.21/0.56    inference(cnf_transformation,[],[f22])).
% 0.21/0.56  fof(f22,plain,(
% 0.21/0.56    ? [X0,X1,X2] : (~r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v2_funct_1(X2) & r1_xboole_0(X0,X1) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.21/0.56    inference(flattening,[],[f21])).
% 0.21/0.56  fof(f21,plain,(
% 0.21/0.56    ? [X0,X1,X2] : ((~r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & (v2_funct_1(X2) & r1_xboole_0(X0,X1))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.21/0.56    inference(ennf_transformation,[],[f19])).
% 0.21/0.56  fof(f19,negated_conjecture,(
% 0.21/0.56    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_xboole_0(X0,X1)) => r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.21/0.56    inference(negated_conjecture,[],[f18])).
% 0.21/0.56  fof(f18,conjecture,(
% 0.21/0.56    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_xboole_0(X0,X1)) => r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_funct_1)).
% 0.21/0.56  fof(f52,plain,(
% 0.21/0.56    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f23])).
% 0.21/0.56  fof(f23,plain,(
% 0.21/0.56    ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f9])).
% 0.21/0.56  fof(f9,axiom,(
% 0.21/0.56    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_relat_1)).
% 0.21/0.56  fof(f1065,plain,(
% 0.21/0.56    k1_xboole_0 = k1_relat_1(k7_relat_1(sK2,k1_xboole_0))),
% 0.21/0.56    inference(resolution,[],[f155,f43])).
% 0.21/0.56  fof(f155,plain,(
% 0.21/0.56    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k1_relat_1(k7_relat_1(X0,k1_xboole_0))) )),
% 0.21/0.56    inference(resolution,[],[f125,f61])).
% 0.21/0.56  fof(f61,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = X0) )),
% 0.21/0.56    inference(cnf_transformation,[],[f30])).
% 0.21/0.56  fof(f30,plain,(
% 0.21/0.56    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.56    inference(flattening,[],[f29])).
% 0.21/0.56  fof(f29,plain,(
% 0.21/0.56    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.21/0.56    inference(ennf_transformation,[],[f15])).
% 0.21/0.56  fof(f15,axiom,(
% 0.21/0.56    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 0.21/0.56  fof(f125,plain,(
% 0.21/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f119,f75])).
% 0.21/0.56  fof(f119,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(k4_tarski(sK5(k1_xboole_0,X0),sK6(k1_xboole_0,X0)),k1_xboole_0) | r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.56    inference(resolution,[],[f97,f55])).
% 0.21/0.56  fof(f55,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f26])).
% 0.21/0.56  fof(f26,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0))) | ~v1_relat_1(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f6])).
% 0.21/0.56  fof(f6,axiom,(
% 0.21/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) => r2_hidden(k4_tarski(X2,X3),X1))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).
% 0.21/0.56  fof(f97,plain,(
% 0.21/0.56    v1_relat_1(k1_xboole_0)),
% 0.21/0.56    inference(resolution,[],[f75,f58])).
% 0.21/0.56  fof(f58,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(sK7(X0),X0) | v1_relat_1(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f27])).
% 0.21/0.56  fof(f27,plain,(
% 0.21/0.56    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f5])).
% 0.21/0.56  fof(f5,axiom,(
% 0.21/0.56    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).
% 0.21/0.56  fof(f242,plain,(
% 0.21/0.56    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(k1_xboole_0)) | r2_hidden(sK10(k1_xboole_0),k1_relat_1(k1_xboole_0))) )),
% 0.21/0.56    inference(forward_demodulation,[],[f241,f73])).
% 0.21/0.56  fof(f241,plain,(
% 0.21/0.56    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(k1_xboole_0)) | r2_hidden(sK10(k7_relat_1(sK2,k1_xboole_0)),k1_relat_1(k7_relat_1(sK2,k1_xboole_0)))) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f240,f97])).
% 0.21/0.56  fof(f240,plain,(
% 0.21/0.56    ( ! [X0] : (~v1_relat_1(k1_xboole_0) | ~r2_hidden(X0,k2_relat_1(k1_xboole_0)) | r2_hidden(sK10(k7_relat_1(sK2,k1_xboole_0)),k1_relat_1(k7_relat_1(sK2,k1_xboole_0)))) )),
% 0.21/0.56    inference(forward_demodulation,[],[f239,f73])).
% 0.21/0.56  fof(f239,plain,(
% 0.21/0.56    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(k1_xboole_0)) | ~v1_relat_1(k7_relat_1(sK2,k1_xboole_0)) | r2_hidden(sK10(k7_relat_1(sK2,k1_xboole_0)),k1_relat_1(k7_relat_1(sK2,k1_xboole_0)))) )),
% 0.21/0.56    inference(superposition,[],[f99,f98])).
% 0.21/0.56  fof(f98,plain,(
% 0.21/0.56    k9_relat_1(sK2,k1_xboole_0) = k2_relat_1(k1_xboole_0)),
% 0.21/0.56    inference(superposition,[],[f77,f73])).
% 0.21/0.56  fof(f77,plain,(
% 0.21/0.56    ( ! [X0] : (k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0)) )),
% 0.21/0.56    inference(resolution,[],[f60,f43])).
% 0.21/0.56  fof(f60,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f28])).
% 0.21/0.56  fof(f28,plain,(
% 0.21/0.56    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.56    inference(ennf_transformation,[],[f10])).
% 0.21/0.56  fof(f10,axiom,(
% 0.21/0.56    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.56  fof(f99,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r2_hidden(X1,k9_relat_1(sK2,X0)) | ~v1_relat_1(k7_relat_1(sK2,X0)) | r2_hidden(sK10(k7_relat_1(sK2,X0)),k1_relat_1(k7_relat_1(sK2,X0)))) )),
% 0.21/0.56    inference(superposition,[],[f62,f77])).
% 0.21/0.56  fof(f62,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1) | r2_hidden(sK10(X1),k1_relat_1(X1))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f32])).
% 0.21/0.56  fof(f32,plain,(
% 0.21/0.56    ! [X0,X1] : (? [X2] : r2_hidden(X2,k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.56    inference(flattening,[],[f31])).
% 0.21/0.56  fof(f31,plain,(
% 0.21/0.56    ! [X0,X1] : ((? [X2] : r2_hidden(X2,k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.21/0.56    inference(ennf_transformation,[],[f11])).
% 0.21/0.56  fof(f11,axiom,(
% 0.21/0.56    ! [X0,X1] : (v1_relat_1(X1) => ~(! [X2] : ~r2_hidden(X2,k1_relat_1(X1)) & r2_hidden(X0,k2_relat_1(X1))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relat_1)).
% 0.21/0.56  fof(f1089,plain,(
% 0.21/0.56    r2_hidden(k4_tarski(sK3(k2_relat_1(k1_xboole_0)),sK4(k2_relat_1(k1_xboole_0))),k2_relat_1(k1_xboole_0)) | k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.56    inference(resolution,[],[f1078,f53])).
% 0.21/0.56  fof(f53,plain,(
% 0.21/0.56    ( ! [X0] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0) | k1_xboole_0 = X0) )),
% 0.21/0.56    inference(cnf_transformation,[],[f25])).
% 0.21/0.56  fof(f25,plain,(
% 0.21/0.56    ! [X0] : (k1_xboole_0 = X0 | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0) | ~v1_relat_1(X0))),
% 0.21/0.56    inference(flattening,[],[f24])).
% 0.21/0.56  fof(f24,plain,(
% 0.21/0.56    ! [X0] : ((k1_xboole_0 = X0 | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)) | ~v1_relat_1(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f14])).
% 0.21/0.56  fof(f14,axiom,(
% 0.21/0.56    ! [X0] : (v1_relat_1(X0) => (! [X1,X2] : ~r2_hidden(k4_tarski(X1,X2),X0) => k1_xboole_0 = X0))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).
% 0.21/0.56  fof(f1078,plain,(
% 0.21/0.56    v1_relat_1(k2_relat_1(k1_xboole_0))),
% 0.21/0.56    inference(subsumption_resolution,[],[f1069,f75])).
% 0.21/0.56  fof(f1069,plain,(
% 0.21/0.56    r2_hidden(sK10(k1_xboole_0),k1_xboole_0) | v1_relat_1(k2_relat_1(k1_xboole_0))),
% 0.21/0.56    inference(backward_demodulation,[],[f135,f1068])).
% 0.21/0.56  fof(f135,plain,(
% 0.21/0.56    r2_hidden(sK10(k1_xboole_0),k1_relat_1(k1_xboole_0)) | v1_relat_1(k2_relat_1(k1_xboole_0))),
% 0.21/0.56    inference(resolution,[],[f81,f97])).
% 0.21/0.56  fof(f81,plain,(
% 0.21/0.56    ( ! [X0] : (~v1_relat_1(X0) | r2_hidden(sK10(X0),k1_relat_1(X0)) | v1_relat_1(k2_relat_1(X0))) )),
% 0.21/0.56    inference(resolution,[],[f62,f58])).
% 0.21/0.56  fof(f430,plain,(
% 0.21/0.56    ~r1_xboole_0(k2_relat_1(k1_xboole_0),k9_relat_1(sK2,sK1))),
% 0.21/0.56    inference(subsumption_resolution,[],[f425,f47])).
% 0.21/0.56  fof(f47,plain,(
% 0.21/0.56    ~r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 0.21/0.56    inference(cnf_transformation,[],[f22])).
% 0.21/0.56  fof(f425,plain,(
% 0.21/0.56    ~r1_xboole_0(k2_relat_1(k1_xboole_0),k9_relat_1(sK2,sK1)) | r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 0.21/0.56    inference(superposition,[],[f136,f179])).
% 0.21/0.56  fof(f179,plain,(
% 0.21/0.56    k2_relat_1(k1_xboole_0) = k9_relat_1(sK2,k3_xboole_0(sK0,sK1))),
% 0.21/0.56    inference(superposition,[],[f77,f108])).
% 0.21/0.56  fof(f108,plain,(
% 0.21/0.56    k1_xboole_0 = k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),
% 0.21/0.56    inference(resolution,[],[f90,f45])).
% 0.21/0.56  fof(f45,plain,(
% 0.21/0.56    r1_xboole_0(sK0,sK1)),
% 0.21/0.56    inference(cnf_transformation,[],[f22])).
% 0.21/0.56  fof(f90,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k7_relat_1(sK2,k3_xboole_0(X0,X1))) )),
% 0.21/0.56    inference(backward_demodulation,[],[f86,f88])).
% 0.21/0.56  fof(f88,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK2,X0),X1) = k7_relat_1(sK2,k3_xboole_0(X0,X1))) )),
% 0.21/0.56    inference(resolution,[],[f67,f43])).
% 0.21/0.56  fof(f67,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f38])).
% 0.21/0.56  fof(f38,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.21/0.56    inference(ennf_transformation,[],[f8])).
% 0.21/0.56  fof(f8,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).
% 0.21/0.56  fof(f86,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,X0),X1)) )),
% 0.21/0.56    inference(resolution,[],[f68,f43])).
% 0.21/0.56  fof(f68,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_xboole_0(X0,X1) | k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f40])).
% 0.21/0.56  fof(f40,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2))),
% 0.21/0.56    inference(flattening,[],[f39])).
% 0.21/0.56  fof(f39,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.21/0.56    inference(ennf_transformation,[],[f12])).
% 0.21/0.56  fof(f12,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).
% 0.21/0.56  fof(f136,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r1_xboole_0(k9_relat_1(sK2,k3_xboole_0(X0,X1)),k9_relat_1(sK2,X1)) | r1_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) )),
% 0.21/0.56    inference(superposition,[],[f65,f96])).
% 0.21/0.56  fof(f96,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k9_relat_1(sK2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f95,f43])).
% 0.21/0.56  fof(f95,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~v1_relat_1(sK2) | k9_relat_1(sK2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f94,f44])).
% 0.21/0.56  fof(f44,plain,(
% 0.21/0.56    v1_funct_1(sK2)),
% 0.21/0.56    inference(cnf_transformation,[],[f22])).
% 0.21/0.56  fof(f94,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k9_relat_1(sK2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) )),
% 0.21/0.56    inference(resolution,[],[f69,f46])).
% 0.21/0.56  fof(f46,plain,(
% 0.21/0.56    v2_funct_1(sK2)),
% 0.21/0.56    inference(cnf_transformation,[],[f22])).
% 0.21/0.56  fof(f69,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f42])).
% 0.21/0.56  fof(f42,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.56    inference(flattening,[],[f41])).
% 0.21/0.56  fof(f41,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.56    inference(ennf_transformation,[],[f17])).
% 0.21/0.56  fof(f17,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_1)).
% 0.21/0.56  fof(f65,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f36])).
% 0.21/0.56  fof(f36,plain,(
% 0.21/0.56    ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1))),
% 0.21/0.56    inference(ennf_transformation,[],[f3])).
% 0.21/0.56  fof(f3,axiom,(
% 0.21/0.56    ! [X0,X1] : ~(r1_xboole_0(k3_xboole_0(X0,X1),X1) & ~r1_xboole_0(X0,X1))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_xboole_1)).
% 0.21/0.56  % SZS output end Proof for theBenchmark
% 0.21/0.56  % (15765)------------------------------
% 0.21/0.56  % (15765)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (15765)Termination reason: Refutation
% 0.21/0.56  
% 0.21/0.56  % (15765)Memory used [KB]: 2558
% 0.21/0.56  % (15765)Time elapsed: 0.111 s
% 0.21/0.56  % (15765)------------------------------
% 0.21/0.56  % (15765)------------------------------
% 0.21/0.56  % (15747)Success in time 0.198 s
%------------------------------------------------------------------------------
