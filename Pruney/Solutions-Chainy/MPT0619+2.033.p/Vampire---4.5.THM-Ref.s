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
% DateTime   : Thu Dec  3 12:51:51 EST 2020

% Result     : Theorem 1.84s
% Output     : Refutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   94 (3006 expanded)
%              Number of leaves         :   10 ( 745 expanded)
%              Depth                    :   28
%              Number of atoms          :  248 (7442 expanded)
%              Number of equality atoms :  139 (4721 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f404,plain,(
    $false ),
    inference(subsumption_resolution,[],[f403,f333])).

fof(f333,plain,(
    r2_hidden(sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f298,f325])).

fof(f325,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f322,f295])).

fof(f295,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f21,f294])).

fof(f294,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f284,f21])).

fof(f284,plain,
    ( ~ v1_relat_1(sK1)
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f283])).

fof(f283,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v1_relat_1(sK1)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f27,f260])).

fof(f260,plain,(
    k1_xboole_0 = k2_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f259,f52])).

fof(f52,plain,(
    k2_relat_1(sK1) != k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) ),
    inference(definition_unfolding,[],[f24,f51])).

fof(f51,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f25,f50])).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f36,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f39,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f36,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f25,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f24,plain,(
    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( k1_tarski(X0) = k1_relat_1(X1)
         => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

fof(f259,plain,
    ( k1_xboole_0 = k2_relat_1(sK1)
    | k2_relat_1(sK1) = k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) ),
    inference(equality_resolution,[],[f256])).

fof(f256,plain,(
    ! [X2] :
      ( k1_funct_1(sK1,sK0) != X2
      | k1_xboole_0 = k2_relat_1(sK1)
      | k2_relat_1(sK1) = k3_enumset1(X2,X2,X2,X2,X2) ) ),
    inference(duplicate_literal_removal,[],[f255])).

fof(f255,plain,(
    ! [X2] :
      ( k1_funct_1(sK1,sK0) != X2
      | k1_xboole_0 = k2_relat_1(sK1)
      | k2_relat_1(sK1) = k3_enumset1(X2,X2,X2,X2,X2)
      | k1_xboole_0 = k2_relat_1(sK1)
      | k2_relat_1(sK1) = k3_enumset1(X2,X2,X2,X2,X2) ) ),
    inference(superposition,[],[f54,f249])).

fof(f249,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,sK0) = sK5(k2_relat_1(sK1),X0)
      | k1_xboole_0 = k2_relat_1(sK1)
      | k2_relat_1(sK1) = k3_enumset1(X0,X0,X0,X0,X0) ) ),
    inference(subsumption_resolution,[],[f244,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | k1_xboole_0 = X0
      | k3_enumset1(X1,X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f37,f51])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_zfmisc_1)).

fof(f244,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,sK0) = sK5(k2_relat_1(sK1),X0)
      | k1_xboole_0 = k2_relat_1(sK1)
      | k2_relat_1(sK1) = k3_enumset1(X0,X0,X0,X0,X0)
      | ~ r2_hidden(sK5(k2_relat_1(sK1),X0),k2_relat_1(sK1)) ) ),
    inference(superposition,[],[f95,f89])).

fof(f89,plain,(
    ! [X0] :
      ( sK0 = sK3(sK1,X0)
      | ~ r2_hidden(X0,k2_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f88,f21])).

fof(f88,plain,(
    ! [X0] :
      ( sK0 = sK3(sK1,X0)
      | ~ v1_relat_1(sK1)
      | ~ r2_hidden(X0,k2_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f85,f22])).

fof(f22,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f85,plain,(
    ! [X0] :
      ( sK0 = sK3(sK1,X0)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1)
      | ~ r2_hidden(X0,k2_relat_1(sK1)) ) ),
    inference(resolution,[],[f83,f67])).

fof(f67,plain,(
    ! [X2,X0] :
      ( r2_hidden(sK3(X0,X2),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK3(X0,X2),k1_relat_1(X0))
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(f83,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | sK0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f79])).

fof(f79,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | sK0 = X0
      | sK0 = X0
      | sK0 = X0 ) ),
    inference(superposition,[],[f74,f53])).

fof(f53,plain,(
    k1_relat_1(sK1) = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f23,f51])).

fof(f23,plain,(
    k1_tarski(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f74,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,k3_enumset1(X0,X0,X0,X1,X2))
      | X1 = X4
      | X2 = X4
      | X0 = X4 ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f45,f49])).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f95,plain,(
    ! [X1] :
      ( sK5(k2_relat_1(sK1),X1) = k1_funct_1(sK1,sK3(sK1,sK5(k2_relat_1(sK1),X1)))
      | k1_xboole_0 = k2_relat_1(sK1)
      | k2_relat_1(sK1) = k3_enumset1(X1,X1,X1,X1,X1) ) ),
    inference(resolution,[],[f78,f55])).

fof(f78,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_relat_1(sK1))
      | k1_funct_1(sK1,sK3(sK1,X1)) = X1 ) ),
    inference(subsumption_resolution,[],[f76,f21])).

fof(f76,plain,(
    ! [X1] :
      ( ~ v1_relat_1(sK1)
      | k1_funct_1(sK1,sK3(sK1,X1)) = X1
      | ~ r2_hidden(X1,k2_relat_1(sK1)) ) ),
    inference(resolution,[],[f22,f66])).

fof(f66,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_funct_1(X0,sK3(X0,X2)) = X2
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK3(X0,X2)) = X2
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f54,plain,(
    ! [X0,X1] :
      ( sK5(X0,X1) != X1
      | k1_xboole_0 = X0
      | k3_enumset1(X1,X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f38,f51])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | sK5(X0,X1) != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f21,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f322,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f320])).

fof(f320,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0)
    | k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f28,f307])).

fof(f307,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f260,f294])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(f298,plain,(
    r2_hidden(sK0,k1_relat_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f80,f294])).

fof(f80,plain,(
    r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(superposition,[],[f73,f53])).

fof(f73,plain,(
    ! [X4,X2,X1] : r2_hidden(X4,k3_enumset1(X4,X4,X4,X1,X2)) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X4,X2,X3,X1] :
      ( r2_hidden(X4,X3)
      | k3_enumset1(X4,X4,X4,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 != X4
      | r2_hidden(X4,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f46,f49])).

fof(f46,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 != X4
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f403,plain,(
    ~ r2_hidden(sK0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f402,f332])).

fof(f332,plain,(
    k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(backward_demodulation,[],[f297,f325])).

fof(f297,plain,(
    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k1_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f53,f294])).

fof(f402,plain,
    ( k1_xboole_0 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | ~ r2_hidden(sK0,k1_xboole_0) ),
    inference(superposition,[],[f362,f366])).

fof(f366,plain,(
    ! [X0] :
      ( sK0 = k1_funct_1(k1_xboole_0,X0)
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f365,f345])).

fof(f345,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | sK0 = X0 ) ),
    inference(forward_demodulation,[],[f299,f325])).

fof(f299,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(k1_xboole_0))
      | sK0 = X0 ) ),
    inference(backward_demodulation,[],[f83,f294])).

fof(f365,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(k1_xboole_0,X0),k1_xboole_0)
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f364,f325])).

fof(f364,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(k1_xboole_0))
      | r2_hidden(k1_funct_1(k1_xboole_0,X0),k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f363,f294])).

fof(f363,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(k1_xboole_0,X0),k1_xboole_0)
      | ~ r2_hidden(X0,k1_relat_1(sK1)) ) ),
    inference(forward_demodulation,[],[f292,f294])).

fof(f292,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK1,X0),k1_xboole_0)
      | ~ r2_hidden(X0,k1_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f291,f21])).

fof(f291,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK1,X0),k1_xboole_0)
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f281,f22])).

fof(f281,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK1,X0),k1_xboole_0)
      | ~ v1_funct_1(sK1)
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f65,f260])).

fof(f65,plain,(
    ! [X0,X3] :
      ( r2_hidden(k1_funct_1(X0,X3),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | r2_hidden(k1_funct_1(X0,X3),X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X0,X3) != X2
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f362,plain,(
    k1_xboole_0 != k3_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0)) ),
    inference(forward_demodulation,[],[f261,f294])).

fof(f261,plain,(
    k1_xboole_0 != k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) ),
    inference(backward_demodulation,[],[f52,f260])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:32:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.55  % (28382)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.56  % (28398)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.56  % (28385)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.56  % (28390)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.57  % (28402)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.58  % (28391)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.58  % (28410)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.58  % (28383)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.58  % (28405)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.59  % (28397)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.59  % (28403)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.59  % (28387)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.59  % (28384)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.60  % (28396)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.60  % (28389)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.60  % (28411)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.60  % (28388)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.60  % (28404)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.60  % (28393)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.60  % (28395)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.60  % (28400)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.84/0.61  % (28386)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.84/0.61  % (28394)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.84/0.61  % (28399)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.84/0.61  % (28408)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.84/0.61  % (28392)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.84/0.61  % (28409)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.84/0.62  % (28401)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.84/0.62  % (28403)Refutation found. Thanks to Tanya!
% 1.84/0.62  % SZS status Theorem for theBenchmark
% 1.84/0.62  % (28407)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.84/0.62  % (28406)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.98/0.62  % SZS output start Proof for theBenchmark
% 1.98/0.62  fof(f404,plain,(
% 1.98/0.62    $false),
% 1.98/0.62    inference(subsumption_resolution,[],[f403,f333])).
% 1.98/0.62  fof(f333,plain,(
% 1.98/0.62    r2_hidden(sK0,k1_xboole_0)),
% 1.98/0.62    inference(backward_demodulation,[],[f298,f325])).
% 1.98/0.62  fof(f325,plain,(
% 1.98/0.62    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.98/0.62    inference(subsumption_resolution,[],[f322,f295])).
% 1.98/0.62  fof(f295,plain,(
% 1.98/0.62    v1_relat_1(k1_xboole_0)),
% 1.98/0.62    inference(backward_demodulation,[],[f21,f294])).
% 1.98/0.62  fof(f294,plain,(
% 1.98/0.62    k1_xboole_0 = sK1),
% 1.98/0.62    inference(subsumption_resolution,[],[f284,f21])).
% 1.98/0.62  fof(f284,plain,(
% 1.98/0.62    ~v1_relat_1(sK1) | k1_xboole_0 = sK1),
% 1.98/0.62    inference(trivial_inequality_removal,[],[f283])).
% 1.98/0.62  fof(f283,plain,(
% 1.98/0.62    k1_xboole_0 != k1_xboole_0 | ~v1_relat_1(sK1) | k1_xboole_0 = sK1),
% 1.98/0.62    inference(superposition,[],[f27,f260])).
% 1.98/0.62  fof(f260,plain,(
% 1.98/0.62    k1_xboole_0 = k2_relat_1(sK1)),
% 1.98/0.62    inference(subsumption_resolution,[],[f259,f52])).
% 1.98/0.62  fof(f52,plain,(
% 1.98/0.62    k2_relat_1(sK1) != k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))),
% 1.98/0.62    inference(definition_unfolding,[],[f24,f51])).
% 1.98/0.62  fof(f51,plain,(
% 1.98/0.62    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.98/0.62    inference(definition_unfolding,[],[f25,f50])).
% 1.98/0.62  fof(f50,plain,(
% 1.98/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.98/0.62    inference(definition_unfolding,[],[f36,f49])).
% 1.98/0.62  fof(f49,plain,(
% 1.98/0.62    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.98/0.62    inference(definition_unfolding,[],[f39,f40])).
% 1.98/0.62  fof(f40,plain,(
% 1.98/0.62    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.98/0.62    inference(cnf_transformation,[],[f5])).
% 1.98/0.62  fof(f5,axiom,(
% 1.98/0.62    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.98/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.98/0.62  fof(f39,plain,(
% 1.98/0.62    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.98/0.62    inference(cnf_transformation,[],[f4])).
% 1.98/0.62  fof(f4,axiom,(
% 1.98/0.62    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.98/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.98/0.62  fof(f36,plain,(
% 1.98/0.62    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.98/0.62    inference(cnf_transformation,[],[f3])).
% 1.98/0.62  fof(f3,axiom,(
% 1.98/0.62    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.98/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.98/0.62  fof(f25,plain,(
% 1.98/0.62    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.98/0.62    inference(cnf_transformation,[],[f2])).
% 1.98/0.62  fof(f2,axiom,(
% 1.98/0.62    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.98/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.98/0.62  fof(f24,plain,(
% 1.98/0.62    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0))),
% 1.98/0.62    inference(cnf_transformation,[],[f13])).
% 1.98/0.62  fof(f13,plain,(
% 1.98/0.62    ? [X0,X1] : (k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.98/0.62    inference(flattening,[],[f12])).
% 1.98/0.62  fof(f12,plain,(
% 1.98/0.62    ? [X0,X1] : ((k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.98/0.62    inference(ennf_transformation,[],[f11])).
% 1.98/0.62  fof(f11,negated_conjecture,(
% 1.98/0.62    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.98/0.62    inference(negated_conjecture,[],[f10])).
% 1.98/0.62  fof(f10,conjecture,(
% 1.98/0.62    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.98/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).
% 1.98/0.62  fof(f259,plain,(
% 1.98/0.62    k1_xboole_0 = k2_relat_1(sK1) | k2_relat_1(sK1) = k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))),
% 1.98/0.62    inference(equality_resolution,[],[f256])).
% 1.98/0.62  fof(f256,plain,(
% 1.98/0.62    ( ! [X2] : (k1_funct_1(sK1,sK0) != X2 | k1_xboole_0 = k2_relat_1(sK1) | k2_relat_1(sK1) = k3_enumset1(X2,X2,X2,X2,X2)) )),
% 1.98/0.62    inference(duplicate_literal_removal,[],[f255])).
% 1.98/0.62  fof(f255,plain,(
% 1.98/0.62    ( ! [X2] : (k1_funct_1(sK1,sK0) != X2 | k1_xboole_0 = k2_relat_1(sK1) | k2_relat_1(sK1) = k3_enumset1(X2,X2,X2,X2,X2) | k1_xboole_0 = k2_relat_1(sK1) | k2_relat_1(sK1) = k3_enumset1(X2,X2,X2,X2,X2)) )),
% 1.98/0.62    inference(superposition,[],[f54,f249])).
% 1.98/0.62  fof(f249,plain,(
% 1.98/0.62    ( ! [X0] : (k1_funct_1(sK1,sK0) = sK5(k2_relat_1(sK1),X0) | k1_xboole_0 = k2_relat_1(sK1) | k2_relat_1(sK1) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.98/0.62    inference(subsumption_resolution,[],[f244,f55])).
% 1.98/0.62  fof(f55,plain,(
% 1.98/0.62    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | k1_xboole_0 = X0 | k3_enumset1(X1,X1,X1,X1,X1) = X0) )),
% 1.98/0.62    inference(definition_unfolding,[],[f37,f51])).
% 1.98/0.62  fof(f37,plain,(
% 1.98/0.62    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | r2_hidden(sK5(X0,X1),X0)) )),
% 1.98/0.62    inference(cnf_transformation,[],[f19])).
% 1.98/0.62  fof(f19,plain,(
% 1.98/0.62    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 1.98/0.62    inference(ennf_transformation,[],[f6])).
% 1.98/0.62  fof(f6,axiom,(
% 1.98/0.62    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 1.98/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_zfmisc_1)).
% 1.98/0.62  fof(f244,plain,(
% 1.98/0.62    ( ! [X0] : (k1_funct_1(sK1,sK0) = sK5(k2_relat_1(sK1),X0) | k1_xboole_0 = k2_relat_1(sK1) | k2_relat_1(sK1) = k3_enumset1(X0,X0,X0,X0,X0) | ~r2_hidden(sK5(k2_relat_1(sK1),X0),k2_relat_1(sK1))) )),
% 1.98/0.62    inference(superposition,[],[f95,f89])).
% 1.98/0.62  fof(f89,plain,(
% 1.98/0.62    ( ! [X0] : (sK0 = sK3(sK1,X0) | ~r2_hidden(X0,k2_relat_1(sK1))) )),
% 1.98/0.62    inference(subsumption_resolution,[],[f88,f21])).
% 1.98/0.62  fof(f88,plain,(
% 1.98/0.62    ( ! [X0] : (sK0 = sK3(sK1,X0) | ~v1_relat_1(sK1) | ~r2_hidden(X0,k2_relat_1(sK1))) )),
% 1.98/0.62    inference(subsumption_resolution,[],[f85,f22])).
% 1.98/0.62  fof(f22,plain,(
% 1.98/0.62    v1_funct_1(sK1)),
% 1.98/0.62    inference(cnf_transformation,[],[f13])).
% 1.98/0.62  fof(f85,plain,(
% 1.98/0.62    ( ! [X0] : (sK0 = sK3(sK1,X0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~r2_hidden(X0,k2_relat_1(sK1))) )),
% 1.98/0.62    inference(resolution,[],[f83,f67])).
% 1.98/0.62  fof(f67,plain,(
% 1.98/0.62    ( ! [X2,X0] : (r2_hidden(sK3(X0,X2),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 1.98/0.62    inference(equality_resolution,[],[f33])).
% 1.98/0.62  fof(f33,plain,(
% 1.98/0.62    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK3(X0,X2),k1_relat_1(X0)) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 1.98/0.62    inference(cnf_transformation,[],[f18])).
% 1.98/0.62  fof(f18,plain,(
% 1.98/0.62    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.98/0.62    inference(flattening,[],[f17])).
% 1.98/0.62  fof(f17,plain,(
% 1.98/0.62    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.98/0.62    inference(ennf_transformation,[],[f9])).
% 1.98/0.62  fof(f9,axiom,(
% 1.98/0.62    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 1.98/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).
% 1.98/0.63  fof(f83,plain,(
% 1.98/0.63    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | sK0 = X0) )),
% 1.98/0.63    inference(duplicate_literal_removal,[],[f79])).
% 1.98/0.63  fof(f79,plain,(
% 1.98/0.63    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | sK0 = X0 | sK0 = X0 | sK0 = X0) )),
% 1.98/0.63    inference(superposition,[],[f74,f53])).
% 1.98/0.63  fof(f53,plain,(
% 1.98/0.63    k1_relat_1(sK1) = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 1.98/0.63    inference(definition_unfolding,[],[f23,f51])).
% 1.98/0.63  fof(f23,plain,(
% 1.98/0.63    k1_tarski(sK0) = k1_relat_1(sK1)),
% 1.98/0.63    inference(cnf_transformation,[],[f13])).
% 1.98/0.63  fof(f74,plain,(
% 1.98/0.63    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,k3_enumset1(X0,X0,X0,X1,X2)) | X1 = X4 | X2 = X4 | X0 = X4) )),
% 1.98/0.63    inference(equality_resolution,[],[f59])).
% 1.98/0.63  fof(f59,plain,(
% 1.98/0.63    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 1.98/0.63    inference(definition_unfolding,[],[f45,f49])).
% 1.98/0.63  fof(f45,plain,(
% 1.98/0.63    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.98/0.63    inference(cnf_transformation,[],[f20])).
% 1.98/0.63  fof(f20,plain,(
% 1.98/0.63    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.98/0.63    inference(ennf_transformation,[],[f1])).
% 1.98/0.63  fof(f1,axiom,(
% 1.98/0.63    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.98/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 1.98/0.63  fof(f95,plain,(
% 1.98/0.63    ( ! [X1] : (sK5(k2_relat_1(sK1),X1) = k1_funct_1(sK1,sK3(sK1,sK5(k2_relat_1(sK1),X1))) | k1_xboole_0 = k2_relat_1(sK1) | k2_relat_1(sK1) = k3_enumset1(X1,X1,X1,X1,X1)) )),
% 1.98/0.63    inference(resolution,[],[f78,f55])).
% 1.98/0.63  fof(f78,plain,(
% 1.98/0.63    ( ! [X1] : (~r2_hidden(X1,k2_relat_1(sK1)) | k1_funct_1(sK1,sK3(sK1,X1)) = X1) )),
% 1.98/0.63    inference(subsumption_resolution,[],[f76,f21])).
% 1.98/0.63  fof(f76,plain,(
% 1.98/0.63    ( ! [X1] : (~v1_relat_1(sK1) | k1_funct_1(sK1,sK3(sK1,X1)) = X1 | ~r2_hidden(X1,k2_relat_1(sK1))) )),
% 1.98/0.63    inference(resolution,[],[f22,f66])).
% 1.98/0.63  fof(f66,plain,(
% 1.98/0.63    ( ! [X2,X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_funct_1(X0,sK3(X0,X2)) = X2 | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 1.98/0.63    inference(equality_resolution,[],[f34])).
% 1.98/0.63  fof(f34,plain,(
% 1.98/0.63    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_funct_1(X0,sK3(X0,X2)) = X2 | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 1.98/0.63    inference(cnf_transformation,[],[f18])).
% 1.98/0.63  fof(f54,plain,(
% 1.98/0.63    ( ! [X0,X1] : (sK5(X0,X1) != X1 | k1_xboole_0 = X0 | k3_enumset1(X1,X1,X1,X1,X1) = X0) )),
% 1.98/0.63    inference(definition_unfolding,[],[f38,f51])).
% 1.98/0.63  fof(f38,plain,(
% 1.98/0.63    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | sK5(X0,X1) != X1) )),
% 1.98/0.63    inference(cnf_transformation,[],[f19])).
% 1.98/0.63  fof(f27,plain,(
% 1.98/0.63    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = X0) )),
% 1.98/0.63    inference(cnf_transformation,[],[f15])).
% 1.98/0.63  fof(f15,plain,(
% 1.98/0.63    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.98/0.63    inference(flattening,[],[f14])).
% 1.98/0.63  fof(f14,plain,(
% 1.98/0.63    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.98/0.63    inference(ennf_transformation,[],[f7])).
% 1.98/0.63  fof(f7,axiom,(
% 1.98/0.63    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.98/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 1.98/0.63  fof(f21,plain,(
% 1.98/0.63    v1_relat_1(sK1)),
% 1.98/0.63    inference(cnf_transformation,[],[f13])).
% 1.98/0.63  fof(f322,plain,(
% 1.98/0.63    ~v1_relat_1(k1_xboole_0) | k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.98/0.63    inference(trivial_inequality_removal,[],[f320])).
% 1.98/0.63  fof(f320,plain,(
% 1.98/0.63    k1_xboole_0 != k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.98/0.63    inference(superposition,[],[f28,f307])).
% 1.98/0.63  fof(f307,plain,(
% 1.98/0.63    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.98/0.63    inference(backward_demodulation,[],[f260,f294])).
% 1.98/0.63  fof(f28,plain,(
% 1.98/0.63    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) )),
% 1.98/0.63    inference(cnf_transformation,[],[f16])).
% 1.98/0.63  fof(f16,plain,(
% 1.98/0.63    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.98/0.63    inference(ennf_transformation,[],[f8])).
% 1.98/0.63  fof(f8,axiom,(
% 1.98/0.63    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 1.98/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).
% 1.98/0.63  fof(f298,plain,(
% 1.98/0.63    r2_hidden(sK0,k1_relat_1(k1_xboole_0))),
% 1.98/0.63    inference(backward_demodulation,[],[f80,f294])).
% 1.98/0.63  fof(f80,plain,(
% 1.98/0.63    r2_hidden(sK0,k1_relat_1(sK1))),
% 1.98/0.63    inference(superposition,[],[f73,f53])).
% 1.98/0.63  fof(f73,plain,(
% 1.98/0.63    ( ! [X4,X2,X1] : (r2_hidden(X4,k3_enumset1(X4,X4,X4,X1,X2))) )),
% 1.98/0.63    inference(equality_resolution,[],[f72])).
% 1.98/0.63  fof(f72,plain,(
% 1.98/0.63    ( ! [X4,X2,X3,X1] : (r2_hidden(X4,X3) | k3_enumset1(X4,X4,X4,X1,X2) != X3) )),
% 1.98/0.63    inference(equality_resolution,[],[f58])).
% 1.98/0.63  fof(f58,plain,(
% 1.98/0.63    ( ! [X4,X2,X0,X3,X1] : (X0 != X4 | r2_hidden(X4,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 1.98/0.63    inference(definition_unfolding,[],[f46,f49])).
% 1.98/0.63  fof(f46,plain,(
% 1.98/0.63    ( ! [X4,X2,X0,X3,X1] : (X0 != X4 | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.98/0.63    inference(cnf_transformation,[],[f20])).
% 1.98/0.63  fof(f403,plain,(
% 1.98/0.63    ~r2_hidden(sK0,k1_xboole_0)),
% 1.98/0.63    inference(subsumption_resolution,[],[f402,f332])).
% 1.98/0.63  fof(f332,plain,(
% 1.98/0.63    k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 1.98/0.63    inference(backward_demodulation,[],[f297,f325])).
% 1.98/0.63  fof(f297,plain,(
% 1.98/0.63    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k1_relat_1(k1_xboole_0)),
% 1.98/0.63    inference(backward_demodulation,[],[f53,f294])).
% 1.98/0.63  fof(f402,plain,(
% 1.98/0.63    k1_xboole_0 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) | ~r2_hidden(sK0,k1_xboole_0)),
% 1.98/0.63    inference(superposition,[],[f362,f366])).
% 1.98/0.63  fof(f366,plain,(
% 1.98/0.63    ( ! [X0] : (sK0 = k1_funct_1(k1_xboole_0,X0) | ~r2_hidden(X0,k1_xboole_0)) )),
% 1.98/0.63    inference(resolution,[],[f365,f345])).
% 1.98/0.63  fof(f345,plain,(
% 1.98/0.63    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | sK0 = X0) )),
% 1.98/0.63    inference(forward_demodulation,[],[f299,f325])).
% 1.98/0.63  fof(f299,plain,(
% 1.98/0.63    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(k1_xboole_0)) | sK0 = X0) )),
% 1.98/0.63    inference(backward_demodulation,[],[f83,f294])).
% 1.98/0.63  fof(f365,plain,(
% 1.98/0.63    ( ! [X0] : (r2_hidden(k1_funct_1(k1_xboole_0,X0),k1_xboole_0) | ~r2_hidden(X0,k1_xboole_0)) )),
% 1.98/0.63    inference(forward_demodulation,[],[f364,f325])).
% 1.98/0.63  fof(f364,plain,(
% 1.98/0.63    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(k1_xboole_0)) | r2_hidden(k1_funct_1(k1_xboole_0,X0),k1_xboole_0)) )),
% 1.98/0.63    inference(forward_demodulation,[],[f363,f294])).
% 1.98/0.63  fof(f363,plain,(
% 1.98/0.63    ( ! [X0] : (r2_hidden(k1_funct_1(k1_xboole_0,X0),k1_xboole_0) | ~r2_hidden(X0,k1_relat_1(sK1))) )),
% 1.98/0.63    inference(forward_demodulation,[],[f292,f294])).
% 1.98/0.63  fof(f292,plain,(
% 1.98/0.63    ( ! [X0] : (r2_hidden(k1_funct_1(sK1,X0),k1_xboole_0) | ~r2_hidden(X0,k1_relat_1(sK1))) )),
% 1.98/0.63    inference(subsumption_resolution,[],[f291,f21])).
% 1.98/0.63  fof(f291,plain,(
% 1.98/0.63    ( ! [X0] : (r2_hidden(k1_funct_1(sK1,X0),k1_xboole_0) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_relat_1(sK1)) )),
% 1.98/0.63    inference(subsumption_resolution,[],[f281,f22])).
% 1.98/0.63  fof(f281,plain,(
% 1.98/0.63    ( ! [X0] : (r2_hidden(k1_funct_1(sK1,X0),k1_xboole_0) | ~v1_funct_1(sK1) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_relat_1(sK1)) )),
% 1.98/0.63    inference(superposition,[],[f65,f260])).
% 1.98/0.63  fof(f65,plain,(
% 1.98/0.63    ( ! [X0,X3] : (r2_hidden(k1_funct_1(X0,X3),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~r2_hidden(X3,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.98/0.63    inference(equality_resolution,[],[f64])).
% 1.98/0.63  fof(f64,plain,(
% 1.98/0.63    ( ! [X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(X3,k1_relat_1(X0)) | r2_hidden(k1_funct_1(X0,X3),X1) | k2_relat_1(X0) != X1) )),
% 1.98/0.63    inference(equality_resolution,[],[f35])).
% 1.98/0.63  fof(f35,plain,(
% 1.98/0.63    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(X3,k1_relat_1(X0)) | k1_funct_1(X0,X3) != X2 | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 1.98/0.63    inference(cnf_transformation,[],[f18])).
% 1.98/0.63  fof(f362,plain,(
% 1.98/0.63    k1_xboole_0 != k3_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))),
% 1.98/0.63    inference(forward_demodulation,[],[f261,f294])).
% 1.98/0.63  fof(f261,plain,(
% 1.98/0.63    k1_xboole_0 != k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))),
% 1.98/0.63    inference(backward_demodulation,[],[f52,f260])).
% 1.98/0.63  % SZS output end Proof for theBenchmark
% 1.98/0.63  % (28403)------------------------------
% 1.98/0.63  % (28403)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.98/0.63  % (28403)Termination reason: Refutation
% 1.98/0.63  
% 1.98/0.63  % (28403)Memory used [KB]: 1791
% 1.98/0.63  % (28403)Time elapsed: 0.190 s
% 1.98/0.63  % (28403)------------------------------
% 1.98/0.63  % (28403)------------------------------
% 1.98/0.63  % (28381)Success in time 0.263 s
%------------------------------------------------------------------------------
