%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:51 EST 2020

% Result     : Theorem 1.45s
% Output     : Refutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :   90 (1146 expanded)
%              Number of leaves         :   10 ( 284 expanded)
%              Depth                    :   26
%              Number of atoms          :  232 (2796 expanded)
%              Number of equality atoms :  136 (1799 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f296,plain,(
    $false ),
    inference(subsumption_resolution,[],[f295,f226])).

fof(f226,plain,(
    r2_hidden(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f216,f24])).

fof(f24,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f216,plain,(
    r2_hidden(sK0,k1_relat_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f87,f210])).

fof(f210,plain,(
    k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f209])).

fof(f209,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f75,f190])).

fof(f190,plain,(
    k1_xboole_0 = k2_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f189,f51])).

fof(f51,plain,(
    k2_relat_1(sK1) != k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) ),
    inference(definition_unfolding,[],[f23,f50])).

fof(f50,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f26,f49])).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f35,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f38,f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f38,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f35,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f26,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f23,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

fof(f189,plain,
    ( k1_xboole_0 = k2_relat_1(sK1)
    | k2_relat_1(sK1) = k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) ),
    inference(equality_resolution,[],[f185])).

fof(f185,plain,(
    ! [X3] :
      ( k1_funct_1(sK1,sK0) != X3
      | k1_xboole_0 = k2_relat_1(sK1)
      | k2_relat_1(sK1) = k3_enumset1(X3,X3,X3,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f184])).

fof(f184,plain,(
    ! [X3] :
      ( k1_funct_1(sK1,sK0) != X3
      | k1_xboole_0 = k2_relat_1(sK1)
      | k2_relat_1(sK1) = k3_enumset1(X3,X3,X3,X3,X3)
      | k1_xboole_0 = k2_relat_1(sK1)
      | k2_relat_1(sK1) = k3_enumset1(X3,X3,X3,X3,X3) ) ),
    inference(superposition,[],[f53,f178])).

fof(f178,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,sK0) = sK5(k2_relat_1(sK1),X0)
      | k1_xboole_0 = k2_relat_1(sK1)
      | k2_relat_1(sK1) = k3_enumset1(X0,X0,X0,X0,X0) ) ),
    inference(duplicate_literal_removal,[],[f173])).

fof(f173,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,sK0) = sK5(k2_relat_1(sK1),X0)
      | k1_xboole_0 = k2_relat_1(sK1)
      | k2_relat_1(sK1) = k3_enumset1(X0,X0,X0,X0,X0)
      | k1_xboole_0 = k2_relat_1(sK1)
      | k2_relat_1(sK1) = k3_enumset1(X0,X0,X0,X0,X0) ) ),
    inference(superposition,[],[f97,f94])).

fof(f94,plain,(
    ! [X0] :
      ( sK0 = sK3(sK1,sK5(k2_relat_1(sK1),X0))
      | k1_xboole_0 = k2_relat_1(sK1)
      | k2_relat_1(sK1) = k3_enumset1(X0,X0,X0,X0,X0) ) ),
    inference(resolution,[],[f93,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | k1_xboole_0 = X0
      | k3_enumset1(X1,X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f36,f50])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).

fof(f93,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK1))
      | sK0 = sK3(sK1,X0) ) ),
    inference(resolution,[],[f83,f90])).

fof(f90,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | sK0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f86])).

fof(f86,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | sK0 = X0
      | sK0 = X0
      | sK0 = X0 ) ),
    inference(superposition,[],[f73,f52])).

fof(f52,plain,(
    k1_relat_1(sK1) = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f22,f50])).

fof(f22,plain,(
    k1_tarski(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f73,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,k3_enumset1(X0,X0,X0,X1,X2))
      | X1 = X4
      | X2 = X4
      | X0 = X4 ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f44,f48])).

fof(f44,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f83,plain,(
    ! [X2] :
      ( r2_hidden(sK3(sK1,X2),k1_relat_1(sK1))
      | ~ r2_hidden(X2,k2_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f78,f20])).

fof(f20,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f78,plain,(
    ! [X2] :
      ( ~ v1_relat_1(sK1)
      | r2_hidden(sK3(sK1,X2),k1_relat_1(sK1))
      | ~ r2_hidden(X2,k2_relat_1(sK1)) ) ),
    inference(resolution,[],[f21,f66])).

fof(f66,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(sK3(X0,X2),k1_relat_1(X0))
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK3(X0,X2),k1_relat_1(X0))
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f17])).

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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(f21,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f97,plain,(
    ! [X1] :
      ( sK5(k2_relat_1(sK1),X1) = k1_funct_1(sK1,sK3(sK1,sK5(k2_relat_1(sK1),X1)))
      | k1_xboole_0 = k2_relat_1(sK1)
      | k2_relat_1(sK1) = k3_enumset1(X1,X1,X1,X1,X1) ) ),
    inference(resolution,[],[f84,f54])).

fof(f84,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k2_relat_1(sK1))
      | k1_funct_1(sK1,sK3(sK1,X3)) = X3 ) ),
    inference(subsumption_resolution,[],[f79,f20])).

fof(f79,plain,(
    ! [X3] :
      ( ~ v1_relat_1(sK1)
      | k1_funct_1(sK1,sK3(sK1,X3)) = X3
      | ~ r2_hidden(X3,k2_relat_1(sK1)) ) ),
    inference(resolution,[],[f21,f65])).

fof(f65,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_funct_1(X0,sK3(X0,X2)) = X2
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK3(X0,X2)) = X2
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f53,plain,(
    ! [X0,X1] :
      ( sK5(X0,X1) != X1
      | k1_xboole_0 = X0
      | k3_enumset1(X1,X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f37,f50])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | sK5(X0,X1) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f75,plain,
    ( k1_xboole_0 != k2_relat_1(sK1)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f20,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f87,plain,(
    r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(superposition,[],[f72,f52])).

fof(f72,plain,(
    ! [X4,X2,X1] : r2_hidden(X4,k3_enumset1(X4,X4,X4,X1,X2)) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X4,X2,X3,X1] :
      ( r2_hidden(X4,X3)
      | k3_enumset1(X4,X4,X4,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 != X4
      | r2_hidden(X4,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f45,f48])).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 != X4
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f295,plain,(
    ~ r2_hidden(sK0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f294,f225])).

fof(f225,plain,(
    k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(forward_demodulation,[],[f214,f24])).

fof(f214,plain,(
    k1_relat_1(k1_xboole_0) = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(backward_demodulation,[],[f52,f210])).

fof(f294,plain,
    ( k1_xboole_0 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | ~ r2_hidden(sK0,k1_xboole_0) ),
    inference(superposition,[],[f264,f265])).

fof(f265,plain,(
    ! [X0] :
      ( sK0 = k1_funct_1(k1_xboole_0,X0)
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f255,f227])).

fof(f227,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | sK0 = X0 ) ),
    inference(forward_demodulation,[],[f217,f24])).

fof(f217,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(k1_xboole_0))
      | sK0 = X0 ) ),
    inference(backward_demodulation,[],[f90,f210])).

fof(f255,plain,(
    ! [X4] :
      ( r2_hidden(k1_funct_1(k1_xboole_0,X4),k1_xboole_0)
      | ~ r2_hidden(X4,k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f254,f25])).

fof(f25,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f254,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k1_xboole_0)
      | r2_hidden(k1_funct_1(k1_xboole_0,X4),k2_relat_1(k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f253,f24])).

fof(f253,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k1_relat_1(k1_xboole_0))
      | r2_hidden(k1_funct_1(k1_xboole_0,X4),k2_relat_1(k1_xboole_0)) ) ),
    inference(subsumption_resolution,[],[f242,f212])).

fof(f212,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f20,f210])).

fof(f242,plain,(
    ! [X4] :
      ( ~ v1_relat_1(k1_xboole_0)
      | ~ r2_hidden(X4,k1_relat_1(k1_xboole_0))
      | r2_hidden(k1_funct_1(k1_xboole_0,X4),k2_relat_1(k1_xboole_0)) ) ),
    inference(resolution,[],[f213,f64])).

fof(f64,plain,(
    ! [X0,X3] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | r2_hidden(k1_funct_1(X0,X3),k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | r2_hidden(k1_funct_1(X0,X3),X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X0,X3) != X2
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f213,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f21,f210])).

fof(f264,plain,(
    k1_xboole_0 != k3_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0)) ),
    inference(forward_demodulation,[],[f191,f210])).

fof(f191,plain,(
    k1_xboole_0 != k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) ),
    inference(backward_demodulation,[],[f51,f190])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:40:48 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.51  % (5053)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (5070)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.52  % (5059)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (5063)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.53  % (5078)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.31/0.53  % (5057)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.31/0.53  % (5058)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.31/0.53  % (5080)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.31/0.53  % (5075)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.31/0.53  % (5055)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.31/0.54  % (5065)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.31/0.54  % (5056)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.31/0.54  % (5067)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.31/0.54  % (5068)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.31/0.54  % (5054)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.31/0.54  % (5061)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.31/0.54  % (5076)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.31/0.54  % (5081)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.31/0.54  % (5079)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.31/0.54  % (5060)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.45/0.55  % (5073)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.45/0.55  % (5072)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.45/0.55  % (5066)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.45/0.55  % (5069)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.45/0.55  % (5070)Refutation not found, incomplete strategy% (5070)------------------------------
% 1.45/0.55  % (5070)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.55  % (5070)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.55  
% 1.45/0.55  % (5070)Memory used [KB]: 10746
% 1.45/0.55  % (5070)Time elapsed: 0.142 s
% 1.45/0.55  % (5070)------------------------------
% 1.45/0.55  % (5070)------------------------------
% 1.45/0.55  % (5071)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.45/0.55  % (5077)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.45/0.55  % (5064)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.45/0.55  % (5082)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.45/0.56  % (5074)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.45/0.56  % (5074)Refutation found. Thanks to Tanya!
% 1.45/0.56  % SZS status Theorem for theBenchmark
% 1.45/0.56  % (5062)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.45/0.58  % SZS output start Proof for theBenchmark
% 1.45/0.58  fof(f296,plain,(
% 1.45/0.58    $false),
% 1.45/0.58    inference(subsumption_resolution,[],[f295,f226])).
% 1.45/0.58  fof(f226,plain,(
% 1.45/0.58    r2_hidden(sK0,k1_xboole_0)),
% 1.45/0.58    inference(forward_demodulation,[],[f216,f24])).
% 1.45/0.58  fof(f24,plain,(
% 1.45/0.58    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.45/0.58    inference(cnf_transformation,[],[f7])).
% 1.45/0.58  fof(f7,axiom,(
% 1.45/0.58    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.45/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 1.45/0.58  fof(f216,plain,(
% 1.45/0.58    r2_hidden(sK0,k1_relat_1(k1_xboole_0))),
% 1.45/0.58    inference(backward_demodulation,[],[f87,f210])).
% 1.45/0.58  fof(f210,plain,(
% 1.45/0.58    k1_xboole_0 = sK1),
% 1.45/0.58    inference(trivial_inequality_removal,[],[f209])).
% 1.45/0.58  fof(f209,plain,(
% 1.45/0.58    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1),
% 1.45/0.58    inference(superposition,[],[f75,f190])).
% 1.45/0.58  fof(f190,plain,(
% 1.45/0.58    k1_xboole_0 = k2_relat_1(sK1)),
% 1.45/0.58    inference(subsumption_resolution,[],[f189,f51])).
% 1.45/0.58  fof(f51,plain,(
% 1.45/0.58    k2_relat_1(sK1) != k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))),
% 1.45/0.58    inference(definition_unfolding,[],[f23,f50])).
% 1.45/0.58  fof(f50,plain,(
% 1.45/0.58    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.45/0.58    inference(definition_unfolding,[],[f26,f49])).
% 1.45/0.58  fof(f49,plain,(
% 1.45/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.45/0.58    inference(definition_unfolding,[],[f35,f48])).
% 1.45/0.58  fof(f48,plain,(
% 1.45/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.45/0.58    inference(definition_unfolding,[],[f38,f39])).
% 1.45/0.58  fof(f39,plain,(
% 1.45/0.58    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.45/0.58    inference(cnf_transformation,[],[f5])).
% 1.45/0.58  fof(f5,axiom,(
% 1.45/0.58    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.45/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.45/0.58  fof(f38,plain,(
% 1.45/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.45/0.58    inference(cnf_transformation,[],[f4])).
% 1.45/0.58  fof(f4,axiom,(
% 1.45/0.58    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.45/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.45/0.58  fof(f35,plain,(
% 1.45/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.45/0.58    inference(cnf_transformation,[],[f3])).
% 1.45/0.58  fof(f3,axiom,(
% 1.45/0.58    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.45/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.45/0.58  fof(f26,plain,(
% 1.45/0.58    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.45/0.58    inference(cnf_transformation,[],[f2])).
% 1.45/0.58  fof(f2,axiom,(
% 1.45/0.58    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.45/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.45/0.58  fof(f23,plain,(
% 1.45/0.58    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0))),
% 1.45/0.58    inference(cnf_transformation,[],[f13])).
% 1.45/0.58  fof(f13,plain,(
% 1.45/0.58    ? [X0,X1] : (k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.45/0.58    inference(flattening,[],[f12])).
% 1.45/0.58  fof(f12,plain,(
% 1.45/0.58    ? [X0,X1] : ((k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.45/0.58    inference(ennf_transformation,[],[f11])).
% 1.45/0.58  fof(f11,negated_conjecture,(
% 1.45/0.58    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.45/0.58    inference(negated_conjecture,[],[f10])).
% 1.45/0.58  fof(f10,conjecture,(
% 1.45/0.58    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.45/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).
% 1.45/0.58  fof(f189,plain,(
% 1.45/0.58    k1_xboole_0 = k2_relat_1(sK1) | k2_relat_1(sK1) = k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))),
% 1.45/0.58    inference(equality_resolution,[],[f185])).
% 1.45/0.58  fof(f185,plain,(
% 1.45/0.58    ( ! [X3] : (k1_funct_1(sK1,sK0) != X3 | k1_xboole_0 = k2_relat_1(sK1) | k2_relat_1(sK1) = k3_enumset1(X3,X3,X3,X3,X3)) )),
% 1.45/0.58    inference(duplicate_literal_removal,[],[f184])).
% 1.45/0.58  fof(f184,plain,(
% 1.45/0.58    ( ! [X3] : (k1_funct_1(sK1,sK0) != X3 | k1_xboole_0 = k2_relat_1(sK1) | k2_relat_1(sK1) = k3_enumset1(X3,X3,X3,X3,X3) | k1_xboole_0 = k2_relat_1(sK1) | k2_relat_1(sK1) = k3_enumset1(X3,X3,X3,X3,X3)) )),
% 1.45/0.58    inference(superposition,[],[f53,f178])).
% 1.45/0.58  fof(f178,plain,(
% 1.45/0.58    ( ! [X0] : (k1_funct_1(sK1,sK0) = sK5(k2_relat_1(sK1),X0) | k1_xboole_0 = k2_relat_1(sK1) | k2_relat_1(sK1) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.45/0.58    inference(duplicate_literal_removal,[],[f173])).
% 1.45/0.58  fof(f173,plain,(
% 1.45/0.58    ( ! [X0] : (k1_funct_1(sK1,sK0) = sK5(k2_relat_1(sK1),X0) | k1_xboole_0 = k2_relat_1(sK1) | k2_relat_1(sK1) = k3_enumset1(X0,X0,X0,X0,X0) | k1_xboole_0 = k2_relat_1(sK1) | k2_relat_1(sK1) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.45/0.58    inference(superposition,[],[f97,f94])).
% 1.45/0.58  fof(f94,plain,(
% 1.45/0.58    ( ! [X0] : (sK0 = sK3(sK1,sK5(k2_relat_1(sK1),X0)) | k1_xboole_0 = k2_relat_1(sK1) | k2_relat_1(sK1) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.45/0.58    inference(resolution,[],[f93,f54])).
% 1.45/0.58  fof(f54,plain,(
% 1.45/0.58    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | k1_xboole_0 = X0 | k3_enumset1(X1,X1,X1,X1,X1) = X0) )),
% 1.45/0.58    inference(definition_unfolding,[],[f36,f50])).
% 1.45/0.58  fof(f36,plain,(
% 1.45/0.58    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | r2_hidden(sK5(X0,X1),X0)) )),
% 1.45/0.58    inference(cnf_transformation,[],[f18])).
% 1.45/0.58  fof(f18,plain,(
% 1.45/0.58    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 1.45/0.58    inference(ennf_transformation,[],[f6])).
% 1.45/0.58  fof(f6,axiom,(
% 1.45/0.58    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 1.45/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).
% 1.45/0.58  fof(f93,plain,(
% 1.45/0.58    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK1)) | sK0 = sK3(sK1,X0)) )),
% 1.45/0.58    inference(resolution,[],[f83,f90])).
% 1.45/0.58  fof(f90,plain,(
% 1.45/0.58    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | sK0 = X0) )),
% 1.45/0.58    inference(duplicate_literal_removal,[],[f86])).
% 1.45/0.58  fof(f86,plain,(
% 1.45/0.58    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | sK0 = X0 | sK0 = X0 | sK0 = X0) )),
% 1.45/0.58    inference(superposition,[],[f73,f52])).
% 1.45/0.58  fof(f52,plain,(
% 1.45/0.58    k1_relat_1(sK1) = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 1.45/0.58    inference(definition_unfolding,[],[f22,f50])).
% 1.45/0.58  fof(f22,plain,(
% 1.45/0.58    k1_tarski(sK0) = k1_relat_1(sK1)),
% 1.45/0.58    inference(cnf_transformation,[],[f13])).
% 1.45/0.58  fof(f73,plain,(
% 1.45/0.58    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,k3_enumset1(X0,X0,X0,X1,X2)) | X1 = X4 | X2 = X4 | X0 = X4) )),
% 1.45/0.58    inference(equality_resolution,[],[f58])).
% 1.45/0.58  fof(f58,plain,(
% 1.45/0.58    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 1.45/0.58    inference(definition_unfolding,[],[f44,f48])).
% 1.45/0.58  fof(f44,plain,(
% 1.45/0.58    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.45/0.58    inference(cnf_transformation,[],[f19])).
% 1.45/0.58  fof(f19,plain,(
% 1.45/0.58    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.45/0.58    inference(ennf_transformation,[],[f1])).
% 1.45/0.58  fof(f1,axiom,(
% 1.45/0.58    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.45/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 1.45/0.58  fof(f83,plain,(
% 1.45/0.58    ( ! [X2] : (r2_hidden(sK3(sK1,X2),k1_relat_1(sK1)) | ~r2_hidden(X2,k2_relat_1(sK1))) )),
% 1.45/0.58    inference(subsumption_resolution,[],[f78,f20])).
% 1.45/0.58  fof(f20,plain,(
% 1.45/0.58    v1_relat_1(sK1)),
% 1.45/0.58    inference(cnf_transformation,[],[f13])).
% 1.45/0.58  fof(f78,plain,(
% 1.45/0.58    ( ! [X2] : (~v1_relat_1(sK1) | r2_hidden(sK3(sK1,X2),k1_relat_1(sK1)) | ~r2_hidden(X2,k2_relat_1(sK1))) )),
% 1.45/0.58    inference(resolution,[],[f21,f66])).
% 1.45/0.58  fof(f66,plain,(
% 1.45/0.58    ( ! [X2,X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | r2_hidden(sK3(X0,X2),k1_relat_1(X0)) | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 1.45/0.58    inference(equality_resolution,[],[f32])).
% 1.45/0.58  fof(f32,plain,(
% 1.45/0.58    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK3(X0,X2),k1_relat_1(X0)) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 1.45/0.58    inference(cnf_transformation,[],[f17])).
% 1.45/0.58  fof(f17,plain,(
% 1.45/0.58    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.45/0.58    inference(flattening,[],[f16])).
% 1.45/0.58  fof(f16,plain,(
% 1.45/0.58    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.45/0.58    inference(ennf_transformation,[],[f9])).
% 1.45/0.58  fof(f9,axiom,(
% 1.45/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 1.45/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 1.45/0.58  fof(f21,plain,(
% 1.45/0.58    v1_funct_1(sK1)),
% 1.45/0.58    inference(cnf_transformation,[],[f13])).
% 1.45/0.58  fof(f97,plain,(
% 1.45/0.58    ( ! [X1] : (sK5(k2_relat_1(sK1),X1) = k1_funct_1(sK1,sK3(sK1,sK5(k2_relat_1(sK1),X1))) | k1_xboole_0 = k2_relat_1(sK1) | k2_relat_1(sK1) = k3_enumset1(X1,X1,X1,X1,X1)) )),
% 1.45/0.58    inference(resolution,[],[f84,f54])).
% 1.45/0.58  fof(f84,plain,(
% 1.45/0.58    ( ! [X3] : (~r2_hidden(X3,k2_relat_1(sK1)) | k1_funct_1(sK1,sK3(sK1,X3)) = X3) )),
% 1.45/0.58    inference(subsumption_resolution,[],[f79,f20])).
% 1.45/0.58  fof(f79,plain,(
% 1.45/0.58    ( ! [X3] : (~v1_relat_1(sK1) | k1_funct_1(sK1,sK3(sK1,X3)) = X3 | ~r2_hidden(X3,k2_relat_1(sK1))) )),
% 1.45/0.58    inference(resolution,[],[f21,f65])).
% 1.45/0.58  fof(f65,plain,(
% 1.45/0.58    ( ! [X2,X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_funct_1(X0,sK3(X0,X2)) = X2 | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 1.45/0.58    inference(equality_resolution,[],[f33])).
% 1.45/0.58  fof(f33,plain,(
% 1.45/0.58    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_funct_1(X0,sK3(X0,X2)) = X2 | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 1.45/0.58    inference(cnf_transformation,[],[f17])).
% 1.45/0.58  fof(f53,plain,(
% 1.45/0.58    ( ! [X0,X1] : (sK5(X0,X1) != X1 | k1_xboole_0 = X0 | k3_enumset1(X1,X1,X1,X1,X1) = X0) )),
% 1.45/0.58    inference(definition_unfolding,[],[f37,f50])).
% 1.45/0.58  fof(f37,plain,(
% 1.45/0.58    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | sK5(X0,X1) != X1) )),
% 1.45/0.58    inference(cnf_transformation,[],[f18])).
% 1.45/0.58  fof(f75,plain,(
% 1.45/0.58    k1_xboole_0 != k2_relat_1(sK1) | k1_xboole_0 = sK1),
% 1.45/0.58    inference(resolution,[],[f20,f28])).
% 1.45/0.58  fof(f28,plain,(
% 1.45/0.58    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0) )),
% 1.45/0.58    inference(cnf_transformation,[],[f15])).
% 1.45/0.58  fof(f15,plain,(
% 1.45/0.58    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.45/0.58    inference(flattening,[],[f14])).
% 1.45/0.58  fof(f14,plain,(
% 1.45/0.58    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.45/0.58    inference(ennf_transformation,[],[f8])).
% 1.45/0.58  fof(f8,axiom,(
% 1.45/0.58    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.45/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 1.45/0.58  fof(f87,plain,(
% 1.45/0.58    r2_hidden(sK0,k1_relat_1(sK1))),
% 1.45/0.58    inference(superposition,[],[f72,f52])).
% 1.45/0.58  fof(f72,plain,(
% 1.45/0.58    ( ! [X4,X2,X1] : (r2_hidden(X4,k3_enumset1(X4,X4,X4,X1,X2))) )),
% 1.45/0.58    inference(equality_resolution,[],[f71])).
% 1.45/0.58  fof(f71,plain,(
% 1.45/0.58    ( ! [X4,X2,X3,X1] : (r2_hidden(X4,X3) | k3_enumset1(X4,X4,X4,X1,X2) != X3) )),
% 1.45/0.58    inference(equality_resolution,[],[f57])).
% 1.45/0.58  fof(f57,plain,(
% 1.45/0.58    ( ! [X4,X2,X0,X3,X1] : (X0 != X4 | r2_hidden(X4,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 1.45/0.58    inference(definition_unfolding,[],[f45,f48])).
% 1.45/0.58  fof(f45,plain,(
% 1.45/0.58    ( ! [X4,X2,X0,X3,X1] : (X0 != X4 | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.45/0.58    inference(cnf_transformation,[],[f19])).
% 1.45/0.58  fof(f295,plain,(
% 1.45/0.58    ~r2_hidden(sK0,k1_xboole_0)),
% 1.45/0.58    inference(subsumption_resolution,[],[f294,f225])).
% 1.45/0.58  fof(f225,plain,(
% 1.45/0.58    k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 1.45/0.58    inference(forward_demodulation,[],[f214,f24])).
% 1.45/0.58  fof(f214,plain,(
% 1.45/0.58    k1_relat_1(k1_xboole_0) = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 1.45/0.58    inference(backward_demodulation,[],[f52,f210])).
% 1.45/0.58  fof(f294,plain,(
% 1.45/0.58    k1_xboole_0 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) | ~r2_hidden(sK0,k1_xboole_0)),
% 1.45/0.58    inference(superposition,[],[f264,f265])).
% 1.45/0.58  fof(f265,plain,(
% 1.45/0.58    ( ! [X0] : (sK0 = k1_funct_1(k1_xboole_0,X0) | ~r2_hidden(X0,k1_xboole_0)) )),
% 1.45/0.58    inference(resolution,[],[f255,f227])).
% 1.45/0.58  fof(f227,plain,(
% 1.45/0.58    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | sK0 = X0) )),
% 1.45/0.58    inference(forward_demodulation,[],[f217,f24])).
% 1.45/0.58  fof(f217,plain,(
% 1.45/0.58    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(k1_xboole_0)) | sK0 = X0) )),
% 1.45/0.58    inference(backward_demodulation,[],[f90,f210])).
% 1.45/0.58  fof(f255,plain,(
% 1.45/0.58    ( ! [X4] : (r2_hidden(k1_funct_1(k1_xboole_0,X4),k1_xboole_0) | ~r2_hidden(X4,k1_xboole_0)) )),
% 1.45/0.58    inference(forward_demodulation,[],[f254,f25])).
% 1.45/0.58  fof(f25,plain,(
% 1.45/0.58    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.45/0.58    inference(cnf_transformation,[],[f7])).
% 1.45/0.58  fof(f254,plain,(
% 1.45/0.58    ( ! [X4] : (~r2_hidden(X4,k1_xboole_0) | r2_hidden(k1_funct_1(k1_xboole_0,X4),k2_relat_1(k1_xboole_0))) )),
% 1.45/0.58    inference(forward_demodulation,[],[f253,f24])).
% 1.45/0.58  fof(f253,plain,(
% 1.45/0.58    ( ! [X4] : (~r2_hidden(X4,k1_relat_1(k1_xboole_0)) | r2_hidden(k1_funct_1(k1_xboole_0,X4),k2_relat_1(k1_xboole_0))) )),
% 1.45/0.58    inference(subsumption_resolution,[],[f242,f212])).
% 1.45/0.58  fof(f212,plain,(
% 1.45/0.58    v1_relat_1(k1_xboole_0)),
% 1.45/0.58    inference(backward_demodulation,[],[f20,f210])).
% 1.45/0.58  fof(f242,plain,(
% 1.45/0.58    ( ! [X4] : (~v1_relat_1(k1_xboole_0) | ~r2_hidden(X4,k1_relat_1(k1_xboole_0)) | r2_hidden(k1_funct_1(k1_xboole_0,X4),k2_relat_1(k1_xboole_0))) )),
% 1.45/0.58    inference(resolution,[],[f213,f64])).
% 1.45/0.58  fof(f64,plain,(
% 1.45/0.58    ( ! [X0,X3] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r2_hidden(X3,k1_relat_1(X0)) | r2_hidden(k1_funct_1(X0,X3),k2_relat_1(X0))) )),
% 1.45/0.58    inference(equality_resolution,[],[f63])).
% 1.45/0.58  fof(f63,plain,(
% 1.45/0.58    ( ! [X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(X3,k1_relat_1(X0)) | r2_hidden(k1_funct_1(X0,X3),X1) | k2_relat_1(X0) != X1) )),
% 1.45/0.58    inference(equality_resolution,[],[f34])).
% 1.45/0.58  fof(f34,plain,(
% 1.45/0.58    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(X3,k1_relat_1(X0)) | k1_funct_1(X0,X3) != X2 | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 1.45/0.58    inference(cnf_transformation,[],[f17])).
% 1.45/0.58  fof(f213,plain,(
% 1.45/0.58    v1_funct_1(k1_xboole_0)),
% 1.45/0.58    inference(backward_demodulation,[],[f21,f210])).
% 1.45/0.58  fof(f264,plain,(
% 1.45/0.58    k1_xboole_0 != k3_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))),
% 1.45/0.58    inference(forward_demodulation,[],[f191,f210])).
% 1.45/0.58  fof(f191,plain,(
% 1.45/0.58    k1_xboole_0 != k3_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))),
% 1.45/0.58    inference(backward_demodulation,[],[f51,f190])).
% 1.45/0.58  % SZS output end Proof for theBenchmark
% 1.45/0.58  % (5074)------------------------------
% 1.45/0.58  % (5074)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.58  % (5074)Termination reason: Refutation
% 1.45/0.58  
% 1.45/0.58  % (5074)Memory used [KB]: 1791
% 1.45/0.58  % (5074)Time elapsed: 0.161 s
% 1.45/0.58  % (5074)------------------------------
% 1.45/0.58  % (5074)------------------------------
% 1.45/0.58  % (5051)Success in time 0.226 s
%------------------------------------------------------------------------------
